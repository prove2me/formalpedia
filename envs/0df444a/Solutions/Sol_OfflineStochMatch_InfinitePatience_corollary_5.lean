-- Prove2me | solution 1 for OfflineStochMatch.InfinitePatience.corollary_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:41:20.602905+00:00
-- url     : https://prove2.me/submissions/40d2a50e-1caa-449c-af03-8aa8f48765f3

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting
import Theorems.Thm_OfflineStochMatch_InfinitePatience_lemma_3
import Theorems.Thm_OfflineStochMatch_InfinitePatience_effective_exp_lin
import Theorems.Thm_OfflineStochMatch_InfinitePatience_min_at_zero

namespace OSMCor5

variable {E : Type} [Fintype E] [DecidableEq E]

lemma swap_mem {n : ℕ} (U : Finset E) (a b : E) (ha : a ∈ U) (hb : b ∈ U) (σ : E ≃ Fin n)
    (hσ : ∀ f ∈ U, f ≠ a → σ f < σ a) :
    ∀ f ∈ U, f ≠ b → ((Equiv.swap a b).trans σ) f < ((Equiv.swap a b).trans σ) b := by
  intro f hf hfb
  simp only [Equiv.trans_apply, Equiv.swap_apply_right]
  apply hσ
  · rcases eq_or_ne f a with rfl | hfa
    · rw [Equiv.swap_apply_left]; exact hb
    · rw [Equiv.swap_apply_of_ne_of_ne hfa hfb]; exact hf
  · intro h
    apply hfb
    have := congrArg (Equiv.swap a b) h
    simpa using this

lemma card_before (T : Finset E) (e : E) (he : e ∉ T) :
    ((Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) => ∀ f ∈ T, σ f < σ e)).card : ℝ)
      * (T.card + 1) = ((Fintype.card E).factorial : ℝ) := by
  set n := Fintype.card E
  set U := insert e T with hU
  let B : E → Finset (E ≃ Fin n) := fun g =>
    Finset.univ.filter (fun σ => ∀ f ∈ U, f ≠ g → σ f < σ g)
  have hBe : Finset.univ.filter (fun σ : E ≃ Fin n => ∀ f ∈ T, σ f < σ e) = B e := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B, hU, Finset.mem_insert]
    constructor
    · rintro h f (rfl | hf) hfe
      · exact absurd rfl hfe
      · exact h f hf
    · intro h f hf
      exact h f (Or.inr hf) (by rintro rfl; exact he hf)
  have hcard : ∀ g ∈ U, (B g).card = (B e).card := by
    intro g hg
    have heU : e ∈ U := Finset.mem_insert_self _ _
    apply Finset.card_nbij' (fun σ => (Equiv.swap g e).trans σ) (fun σ => (Equiv.swap e g).trans σ)
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, B] at hσ ⊢
      exact swap_mem U g e hg heU σ hσ
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, B] at hσ ⊢
      exact swap_mem U e g heU hg σ hσ
    · intro σ _
      ext x
      simp [Equiv.swap_comm g e]
    · intro σ _
      ext x
      simp [Equiv.swap_comm g e]
  have hunion : (Finset.univ : Finset (E ≃ Fin n)) = U.biUnion B := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image U (fun f => σ f) ⟨e, Finset.mem_insert_self _ _⟩
    refine ⟨g, hg, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
    intro f hf hfg
    exact lt_of_le_of_ne (hmax f hf) (fun h => hfg (σ.injective h))
  have hdisj : (U : Set E).PairwiseDisjoint B := by
    intro g _ h _ hgh
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ hσg hσh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hσg hσh
    have h1 := hσg h ‹_› (Ne.symm hgh)
    have h2 := hσh g ‹_› hgh
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  have htot : (Finset.univ : Finset (E ≃ Fin n)).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_equiv (Fintype.equivFin E)]
  have hsum : n.factorial = U.card * (B e).card := by
    rw [← htot, hunion, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const,
      smul_eq_mul]
  rw [hBe, hsum, Finset.card_insert_of_notMem he]
  push_cast; ring


lemma perm_avg (N : Finset E) (e : E) (he : e ∉ N) (q : E → ℝ) :
    (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), ∏ f ∈ N.filter (fun f => σ f < σ e), (1 - q f)
      = ∫ x in (0 : ℝ)..1, ∏ f ∈ N, (1 - x * q f) := by
  have hfac : ((Fintype.card E).factorial : ℝ) ≠ 0 := by positivity
  have h1 : ∀ σ : E ≃ Fin (Fintype.card E), ∏ f ∈ N.filter (fun f => σ f < σ e), (1 - q f)
      = ∑ S ∈ N.powerset, if (∀ f ∈ S, σ f < σ e) then ∏ f ∈ S, (-q f) else 0 := by
    intro σ
    rw [Finset.prod_filter]
    rw [show ∏ f ∈ N, (if σ f < σ e then 1 - q f else 1)
        = ∏ f ∈ N, (1 + if σ f < σ e then -q f else 0) from
        Finset.prod_congr rfl (fun f _ => by split_ifs <;> ring)]
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl (fun S _ => by rw [Finset.prod_ite_zero]; congr 1)
  have h2 : ∀ x : ℝ, ∏ f ∈ N, (1 - x * q f) = ∑ S ∈ N.powerset, (∏ f ∈ S, (-q f)) * x ^ S.card := by
    intro x
    rw [show ∏ f ∈ N, (1 - x * q f) = ∏ f ∈ N, (1 + x * (-q f)) from
      Finset.prod_congr rfl (fun f _ => by ring)]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const]; ring
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_finset_sum (fun S _ => by
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have heS : e ∉ S := fun h => he (Finset.mem_powerset.1 hS h)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    intervalIntegral.integral_const_mul, integral_pow]
  have hc := card_before S e heS
  have hS1 : ((S.card : ℝ) + 1) ≠ 0 := by positivity
  have hc' : ((Finset.univ.filter (fun σ : E ≃ Fin (Fintype.card E) => ∀ f ∈ S, σ f < σ e)).card : ℝ)
      = ((Fintype.card E).factorial : ℝ) / (S.card + 1) := by
    rw [eq_div_iff hS1]; exact hc
  rw [hc']
  field_simp
  simp

end OSMCor5

open OfflineStochMatch.InfinitePatience

namespace OSMCor5A

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma coin_sum (y a p : E → ℝ) (e : E) (M : Finset E) (heM : e ∉ M) :
    ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight a A * coinWeight p P *
        (if ((∀ f ∈ M, ¬ (A f = true ∧ P f = true ∧ Y f = true)) ∧ Y e = true ∧ A e = true)
          then (1 : ℝ) else 0)
      = y e * a e * ∏ f ∈ M, (1 - a f * p f * y f) := by
  classical
  let F : E → Bool → Bool → Bool → ℝ := fun f yb ab pb =>
    bern (y f) yb * bern (a f) ab * bern (p f) pb *
      (if ((f = e → yb = true ∧ ab = true) ∧ (f ∈ M → ¬ (ab = true ∧ pb = true ∧ yb = true)))
        then 1 else 0)
  have key : ∀ Y A P : E → Bool,
      coinWeight y Y * coinWeight a A * coinWeight p P *
        (if ((∀ f ∈ M, ¬ (A f = true ∧ P f = true ∧ Y f = true)) ∧ Y e = true ∧ A e = true)
          then (1 : ℝ) else 0) = ∏ f, F f (Y f) (A f) (P f) := by
    intro Y A P
    simp only [F, coinWeight, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_boole]
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; intro f
      refine ⟨fun hf => hf ▸ h1.2, fun hf => h1.1 f hf⟩
    · exfalso; apply h1
      exact ⟨fun f hf => (h2 f).2 hf, (h2 e).1 rfl⟩
    · rfl
  simp_rw [key]
  have s1 : ∀ Y A : E → Bool, ∑ P : E → Bool, ∏ f, F f (Y f) (A f) (P f)
      = ∏ f, ∑ pb, F f (Y f) (A f) pb := fun Y A =>
    (Fintype.prod_sum (fun f pb => F f (Y f) (A f) pb)).symm
  simp_rw [s1]
  have s2 : ∀ Y : E → Bool, ∑ A : E → Bool, ∏ f, ∑ pb, F f (Y f) (A f) pb
      = ∏ f, ∑ ab, ∑ pb, F f (Y f) ab pb := fun Y =>
    (Fintype.prod_sum (fun f ab => ∑ pb, F f (Y f) ab pb)).symm
  simp_rw [s2]
  rw [← Fintype.prod_sum (fun f yb => ∑ ab, ∑ pb, F f yb ab pb)]
  have hfac : ∀ f, ∑ yb, ∑ ab, ∑ pb, F f yb ab pb
      = if f = e then y e * a e else if f ∈ M then 1 - a f * p f * y f else 1 := by
    intro f
    by_cases hfe : f = e
    · subst hfe
      simp [F, bern, Fintype.sum_bool, heM]; ring
    · by_cases hfM : f ∈ M
      · simp [F, bern, Fintype.sum_bool, hfe, hfM]; ring
      · simp [F, bern, Fintype.sum_bool, hfe, hfM]; ring
  simp_rw [hfac]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  simp only [if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun f hf => if_neg (Finset.ne_of_mem_erase hf)), Finset.prod_ite_mem]
  congr 1
  ext f
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨fun hfe => heM (hfe ▸ h), h⟩


lemma matched_sub (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (Y A P : E → Bool)
    (v : V) : ∀ (l : List E) (st : RunState V),
    v ∈ (l.foldl (step G t Y A P) st).matched →
      v ∈ st.matched ∨ ∃ f ∈ l, v ∈ G.ends f ∧ Y f = true ∧ A f = true ∧ P f = true := by
  intro l
  induction l with
  | nil => intro st h; exact Or.inl h
  | cons f l ih =>
    intro st h
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨g, hg, hg'⟩
    · unfold step at h1
      split_ifs at h1 with hc hP
      · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨f, List.mem_cons_self, h1, hc.2.1, hc.2.2, hP⟩
      · exact Or.inl h1
      · exact Or.inl h1
    · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, hg'⟩

lemma safe_free (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (ht : ∀ v, t v = ⊤)
    (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool) (e : E)
    (hs : ∀ f, f ≠ e → (∃ r, r ∈ G.ends e ∧ r ∈ G.ends f) → σ f < σ e →
      ¬ (A f = true ∧ P f = true ∧ Y f = true)) :
    IsFree G t σ Y A P e := by
  intro v hv
  refine ⟨?_, by rw [ht v]; exact ENat.coe_lt_top _⟩
  intro hm
  rcases matched_sub G t Y A P v _ initState hm with h | ⟨f, hf, hvf, hY, hA, hP⟩
  · simp [initState] at h
  · simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    have hlt : σ (σ.symm i) < σ e := by simpa using hi
    have hne : σ.symm i ≠ e := by
      intro h; rw [h] at hlt; exact lt_irrefl _ hlt
    exact hs _ hne ⟨v, hv, hvf⟩ hlt ⟨hA, hP, hY⟩

/-- A toy graph: two edges sharing the vertex `1`. -/
def toyG : EdmondsMatching65.Polyhedron.Graph (Fin 3) (Fin 2) :=
  ⟨fun i => if i = 0 then s(0, 1) else s(1, 2), by intro i; fin_cases i <;> simp⟩

lemma toy_E1 : E1 toyG (fun _ => (1 : ℝ)) 0 1 = {1} := by
  ext f
  fin_cases f <;> simp [E1, delta, toyG, Finset.mem_filter] <;> decide

/-- Per-edge bound `e^{-xz} ≤ 1 - x ã(z) z`, obtained from Lemma 3 on a two-edge graph. -/
lemma edge_bound (aT : ℝ → ℝ) (haT : IsEffective aT) (z x : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : Real.exp (-(x * z)) ≤ 1 - x * aT z * z := by
  have h := lemma_3 toyG (fun _ => (1 : ℝ)) (fun _ => z) aT haT
    (fun _ => ⟨zero_le_one, le_rfl⟩) (fun _ => hz) 0 1 (by simp [toyG]) x hx
  rw [toy_E1, Finset.sum_singleton, Finset.prod_singleton, one_mul] at h
  exact h


open Classical in
/-- The edges `f ≠ e` sharing an endpoint with `e`. -/
noncomputable def Nb (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) : Finset E :=
  Finset.univ.filter (fun f => f ≠ e ∧ ∃ r, r ∈ G.ends e ∧ r ∈ G.ends f)

lemma mem_Nb (G : EdmondsMatching65.Polyhedron.Graph V E) (e f : E) :
    f ∈ Nb G e ↔ f ≠ e ∧ ∃ r, r ∈ G.ends e ∧ r ∈ G.ends f := by
  classical
  simp [Nb]

lemma nbr_sum (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : LPFeasible G p t y) (e : E) :
    ∑ f ∈ Nb G e, p f * y f ≤ 2 * (1 - p e * y e) := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v : V, s(u, v) = G.ends e := by
    obtain ⟨⟨u, v⟩, h⟩ := Sym2.mk_surjective (G.ends e)
    exact ⟨u, v, h⟩
  have hnn : ∀ f, 0 ≤ p f * y f := fun f => mul_nonneg (hp f).1 (hy.1 f).1
  have hsub : Nb G e ⊆ (delta G u).erase e ∪ (delta G v).erase e := by
    intro f hf
    rw [mem_Nb] at hf
    obtain ⟨hne, r, hre, hrf⟩ := hf
    rw [← huv, Sym2.mem_iff] at hre
    simp only [Finset.mem_union, Finset.mem_erase, delta, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rcases hre with rfl | rfl
    · exact Or.inl ⟨hne, hrf⟩
    · exact Or.inr ⟨hne, hrf⟩
  have hdel : ∀ w, w ∈ G.ends e → ∑ f ∈ (delta G w).erase e, p f * y f ≤ 1 - p e * y e := by
    intro w hw
    have he : e ∈ delta G w := by simp [delta, hw]
    rw [Finset.sum_erase_eq_sub he]
    have := hy.2.1 w
    have h2 : ∑ f ∈ delta G w, p f * y f = ∑ f ∈ delta G w, y f * p f :=
      Finset.sum_congr rfl (fun f _ => mul_comm _ _)
    linarith
  have hu : u ∈ G.ends e := by rw [← huv]; exact Sym2.mem_mk_left _ _
  have hv : v ∈ G.ends e := by rw [← huv]; exact Sym2.mem_mk_right _ _
  calc ∑ f ∈ Nb G e, p f * y f
      ≤ ∑ f ∈ (delta G u).erase e ∪ (delta G v).erase e, p f * y f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hnn f)
    _ ≤ ∑ f ∈ (delta G u).erase e, p f * y f + ∑ f ∈ (delta G v).erase e, p f * y f := by
        rw [← Finset.sum_union_inter]
        have : 0 ≤ ∑ f ∈ (delta G u).erase e ∩ (delta G v).erase e, p f * y f :=
          Finset.sum_nonneg (fun f _ => hnn f)
        linarith
    _ ≤ 2 * (1 - p e * y e) := by linarith [hdel u hu, hdel v hv]

lemma pointwise (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞)
    (aT : ℝ → ℝ) (haT : IsEffective aT)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : LPFeasible G p t y) (e : E) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-2 * x * (1 - p e * y e))
      ≤ ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f)) := by
  have hz : ∀ f, p f * y f ∈ Set.Icc (0 : ℝ) 1 := fun f =>
    ⟨mul_nonneg (hp f).1 (hy.1 f).1, mul_le_one₀ (hp f).2 (hy.1 f).1 (hy.1 f).2⟩
  have h1 : ∏ f ∈ Nb G e, Real.exp (-(x * (p f * y f)))
      ≤ ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f)) := by
    apply Finset.prod_le_prod (fun f _ => (Real.exp_pos _).le)
    intro f _
    have := edge_bound aT haT (p f * y f) x (hz f) hx
    calc Real.exp (-(x * (p f * y f))) ≤ 1 - x * aT (p f * y f) * (p f * y f) := this
      _ = 1 - x * (aT (p f * y f) * p f * y f) := by ring
  rw [← Real.exp_sum] at h1
  refine le_trans ?_ h1
  apply Real.exp_le_exp.2
  have hs := nbr_sum G p y t hp hy e
  have : ∑ f ∈ Nb G e, -(x * (p f * y f)) = -(x * ∑ f ∈ Nb G e, p f * y f) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [this]
  have := mul_le_mul_of_nonneg_left hs hx.1
  linarith

lemma cw_nonneg (q : E → ℝ) (hq : ∀ f, 0 ≤ q f ∧ q f ≤ 1) (c : E → Bool) :
    0 ≤ coinWeight q c :=
  Finset.prod_nonneg (fun f _ => by
    unfold bern; split_ifs
    · exact (hq f).1
    · linarith [(hq f).2])

lemma integral_exp_neg_two : (∫ x in (0 : ℝ)..1, Real.exp (-2 * x)) = (1 - Real.exp (-2)) / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by norm_num : (-2 : ℝ) ≠ 0)]
  simp [integral_exp]
  ring

end OSMCor5A

open OSMCor5A in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, t v = ⊤) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    (∫ x in (0 : ℝ)..1, Real.exp (-2 * x)) = (1 - Real.exp (-2)) / 2 ∧
      (1 - Real.exp (-2)) / 2 * y e ≤ probProbed G p t y aT e := by
  classical
  have hEff : IsEffective aT := by
    rcases haT with rfl | rfl
    exacts [effective_exp_lin.1, effective_exp_lin.2]
  refine ⟨integral_exp_neg_two, ?_⟩
  have hz : ∀ f, p f * y f ∈ Set.Icc (0 : ℝ) 1 := fun f =>
    ⟨mul_nonneg (hp f).1 (hy.1 f).1, mul_le_one₀ (hp f).2 (hy.1 f).1 (hy.1 f).2⟩
  have ha : ∀ f, 0 ≤ aT (p f * y f) ∧ aT (p f * y f) ≤ 1 := fun f => hEff.1 _ (hz f)
  have heN : e ∉ Nb G e := by rw [mem_Nb]; exact fun h => h.1 rfl
  -- Step 1: Pr[e probed] ≥ Pr[e safe, Y_e = A_e = 1], computed via independent coins.
  have step1 : (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), y e * aT (p e * y e) *
        ∏ f ∈ (Nb G e).filter (fun f => σ f < σ e), (1 - aT (p f * y f) * p f * y f)
      ≤ probProbed G p t y aT e := by
    unfold probProbed prob
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro σ _
    have hc := coin_sum y (fun f => aT (p f * y f)) p e ((Nb G e).filter (fun f => σ f < σ e))
      (by simp [heN])
    rw [← hc]
    apply Finset.sum_le_sum; intro Y _
    apply Finset.sum_le_sum; intro A _
    apply Finset.sum_le_sum; intro P _
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (mul_nonneg (cw_nonneg y hy.1 Y) (cw_nonneg _ ha A)) (cw_nonneg p hp P))
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      refine ⟨safe_free G t ht σ Y A P e (fun f hne hr hlt => h1.1 f ?_), h1.2.1, h1.2.2⟩
      simp only [Finset.mem_filter, mem_Nb]
      exact ⟨⟨hne, hr⟩, hlt⟩
    · exact zero_le_one
    · exact le_rfl
  -- Step 2: average over the random order.
  have step2 : (1 / ((Fintype.card E).factorial : ℝ)) *
      ∑ σ : E ≃ Fin (Fintype.card E), y e * aT (p e * y e) *
        ∏ f ∈ (Nb G e).filter (fun f => σ f < σ e), (1 - aT (p f * y f) * p f * y f)
      = y e * aT (p e * y e) *
        ∫ x in (0 : ℝ)..1, ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f)) := by
    rw [← OSMCor5.perm_avg (Nb G e) e heN (fun f => aT (p f * y f) * p f * y f),
      ← Finset.mul_sum]
    simp only [mul_assoc]
    ring
  -- Step 3: pointwise lower bound integrated.
  have step3 : (∫ x in (0 : ℝ)..1, Real.exp (-2 * x * (1 - p e * y e)))
      ≤ ∫ x in (0 : ℝ)..1, ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-2 * x * (1 - p e * y e))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ =>
        ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f))).intervalIntegrable _ _
    · intro x hx
      exact pointwise G p y t aT hEff hp hy e x hx
  -- Step 4: minimum at y_e = 0.
  have step4 : (∫ x in (0 : ℝ)..1, Real.exp (-2 * x))
      ≤ aT (p e * y e) * ∫ x in (0 : ℝ)..1, Real.exp (-2 * x * (1 - p e * y e)) := by
    have h := (isMinOn_iff.1 (min_at_zero aT haT)) _ (hz e)
    simpa [hEff.2.1] using h
  calc (1 - Real.exp (-2)) / 2 * y e = y e * ∫ x in (0 : ℝ)..1, Real.exp (-2 * x) := by
        rw [integral_exp_neg_two]; ring
    _ ≤ y e * (aT (p e * y e) * ∫ x in (0 : ℝ)..1, Real.exp (-2 * x * (1 - p e * y e))) :=
        mul_le_mul_of_nonneg_left step4 (hy.1 e).1
    _ ≤ y e * (aT (p e * y e) *
          ∫ x in (0 : ℝ)..1, ∏ f ∈ Nb G e, (1 - x * (aT (p f * y f) * p f * y f))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step3 (ha e).1) (hy.1 e).1
    _ = _ := by rw [step2]; ring
    _ ≤ probProbed G p t y aT e := step1
