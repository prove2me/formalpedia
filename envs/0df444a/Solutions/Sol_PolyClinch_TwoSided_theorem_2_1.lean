-- Prove2me | solution 1 for PolyClinch.TwoSided.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:34:37.567239+00:00
-- url     : https://prove2.me/submissions/887735f8-a902-4aee-902c-4e6a3d55f361
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Market
import Definitions.Def_PolyClinch_TwoSided_Clinching
import Theorems.Thm_PolyClinch_TwoSided_theorem_3_6
import Theorems.Thm_PolyClinch_TwoSided_corollary_3_10
import Theorems.Thm_PolyClinch_TwoSided_proposition_3_8
import Theorems.Thm_PolyClinch_TwoSided_theorem_3_11
import Theorems.Thm_PolyClinch_TwoSided_lemma_3_7

open PolyClinch.TwoSided Finset

namespace PolyClinchThm21Sol

/-- Per-buyer invariant of Algorithm 2. -/
def InvOne (B : WithTop ℝ) (v c p : ℝ) (d : WithTop ℝ) : Prop :=
  0 ≤ c ∧ 0 ≤ d ∧ ((p : ℝ) : WithTop ℝ) ≤ B ∧
    (∀ r : ℝ, d = (r : WithTop ℝ) → ((p + c * r : ℝ) : WithTop ℝ) ≤ B) ∧
    (d = ⊤ → c = 0 ∨ B = ⊤) ∧ (v ≤ c → 0 < c → d = 0)

lemma invOne_demandUpdate (B : WithTop ℝ) (v c p : ℝ) (hc : 0 ≤ c)
    (hp : ((p : ℝ) : WithTop ℝ) ≤ B) : InvOne B v c p (demandUpdate B p c v) := by
  unfold demandUpdate
  by_cases hcv : c < v
  · rw [if_pos hcv]
    by_cases hc0 : c = 0
    · rw [if_pos hc0]
      exact ⟨hc, le_top, hp, fun r hr => (WithTop.top_ne_coe hr).elim, fun _ => Or.inl hc0,
        fun h _ => absurd hcv (not_lt.mpr h)⟩
    · rw [if_neg hc0]
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      induction B using WithTop.recTopCoe with
      | top =>
        refine ⟨hc, le_top, hp, fun r hr => ?_, fun _ => Or.inr rfl,
          fun h _ => absurd hcv (not_lt.mpr h)⟩
        simp at hr
      | coe b =>
        have hpb : p ≤ b := WithTop.coe_le_coe.mp hp
        simp only [WithTop.map_coe]
        refine ⟨hc, ?_, hp, fun r hr => ?_, fun h => ?_, fun h _ => absurd hcv (not_lt.mpr h)⟩
        · exact WithTop.coe_le_coe.mpr (div_nonneg (by linarith) hc)
        · have hr' : (b - p) / c = r := WithTop.coe_injective hr
          rw [← hr']
          have : p + c * ((b - p) / c) = b := by field_simp; ring
          rw [this]
        · exact absurd h WithTop.coe_ne_top
  · rw [if_neg hcv]
    refine ⟨hc, le_refl _, hp, fun r hr => ?_, fun h => ?_, fun _ _ => rfl⟩
    · have : r = 0 := by exact_mod_cast hr.symm
      subst this
      simpa using hp
    · exact absurd h (by simp)

lemma invOne_clinch {B : WithTop ℝ} {v c p : ℝ} {d : WithTop ℝ} (h : InvOne B v c p d)
    {s : ℝ} (_hs : 0 ≤ s) (hsd : ((s : ℝ) : WithTop ℝ) ≤ d) :
    ((p + c * s : ℝ) : WithTop ℝ) ≤ B := by
  obtain ⟨hc, -, hp, hr, htop, -⟩ := h
  induction d using WithTop.recTopCoe with
  | top =>
    rcases htop rfl with h0 | hB
    · subst h0; simpa using hp
    · rw [hB]; exact le_top
  | coe r =>
    have hsr : s ≤ r := WithTop.coe_le_coe.mp hsd
    have h1 := hr r rfl
    induction B using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      have h2 := WithTop.coe_le_coe.mp h1
      have h3 : c * s ≤ c * r := mul_le_mul_of_nonneg_left hsr hc
      exact WithTop.coe_le_coe.mpr (by linarith)

variable {n m : ℕ} (E : Finset (Fin n × Fin m))

/-- Invariant of Algorithm 2 (for fixed clocks `c`). -/
def Inv (I : PublicInfo E) (c : Fin (n + m) → ℝ) (w : ↥(extEdges E) → ℝ)
    (p : Fin (n + m) → ℝ) (d : Fin (n + m) → WithTop ℝ) : Prop :=
  w ∈ extP E I ∧ ∀ k, InvOne (extBudget E I k) (extBid E I k) (c k) (p k) (d k)

lemma clinch_facts (I : PublicInfo E) (w : ↥(extEdges E) → ℝ) (hw : w ∈ extP E I)
    (d : Fin (n + m) → WithTop ℝ) (hd : ∀ k, 0 ≤ d k) (i : Fin (n + m))
    (ξ : ↥(extEdges E) → ℝ) (hξ : ξ ∈ clinchingPolytope E I w d i) :
    w + ξ ∈ extP E I ∧ ((∑ e ∈ extEdgesOfBuyer E i, ξ e : ℝ) : WithTop ℝ) ≤ d i ∧
      (∀ e, 0 ≤ ξ e) := by
  obtain ⟨hξ0, hξoff, hξeq⟩ := hξ
  have h0 : (0 : {k : Fin (n + m) // k ≠ i} → ℝ) ∈ remnantSupplyOthers2 E I w d i 0 := by
    refine ⟨fun _ => le_refl _, 0, ⟨fun _ => le_refl _, by simpa using hw, fun k => ?_⟩,
      fun _ _ => rfl, fun k => by simp⟩
    simpa using hd k
  rw [← hξeq] at h0
  obtain ⟨-, x, ⟨hx0, hxP, hxd⟩, hxi, hxk⟩ := h0
  have hxξ : x = ξ := by
    funext e
    by_cases he : e ∈ extEdgesOfBuyer E i
    · exact hxi e he
    · rw [hξoff e he]
      have hne : e.1.1 ≠ i := by
        intro h; apply he; simp [extEdgesOfBuyer, h]
      have hsum := hxk ⟨e.1.1, hne⟩
      simp only [Pi.zero_apply] at hsum
      have hmem : e ∈ extEdgesOfBuyer E e.1.1 := by simp [extEdgesOfBuyer]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hx0 e)).mp hsum e hmem
  subst hxξ
  exact ⟨hxP, hxd i, hx0⟩

lemma clinch_step (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j))
    (c : Fin (n + m) → ℝ) (i : Fin (n + m)) (u : Alg2Inner E) (hu : Inv E I c u.w u.p u.d) :
    ∃ u', Alg2Clinch E I c i u u' ∧ Inv E I c u'.w u'.p u'.d := by
  have hd : ∀ k, 0 ≤ u.d k := fun k => (hu.2 k).2.1
  obtain ⟨-, ξ, hξ⟩ := theorem_3_6 E I hf u.w hu.1 u.d hd i
  obtain ⟨hwξ, hsd, hξ0⟩ := clinch_facts E I u.w hu.1 u.d hd i ξ hξ.prop
  have hs0 : 0 ≤ ∑ e ∈ extEdgesOfBuyer E i, ξ e := Finset.sum_nonneg (fun e _ => hξ0 e)
  have hpB := invOne_clinch (hu.2 i) hs0 hsd
  refine ⟨⟨u.w + ξ, Function.update u.p i (u.p i + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e),
      Function.update u.d i (demandUpdate (extBudget E I i)
        (u.p i + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e) (c i) (extBid E I i)),
      fun j => u.dr j + ∑ e ∈ extEdgesOfSeller E j, c e.1.1 * ξ e⟩,
    ⟨ξ, hξ, rfl, rfl, ?_, rfl⟩, hwξ, ?_⟩
  · simp
  · intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self]
      exact invOne_demandUpdate _ _ _ _ (hu.2 k).1 hpB
    · simp only [Function.update_of_ne hk]
      exact hu.2 k

lemma inner_exists (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j))
    (c : Fin (n + m) → ℝ) (w : ↥(extEdges E) → ℝ) (p : Fin (n + m) → ℝ)
    (d : Fin (n + m) → WithTop ℝ) (h : Inv E I c w p d) (N : ℕ) :
    ∃ u : ℕ → Alg2Inner E, u 0 = ⟨w, p, d, 0⟩ ∧
      (∀ k (hk : k < n + m), k < N → Alg2Clinch E I c ⟨k, hk⟩ (u k) (u (k + 1))) ∧
      Inv E I c (u N).w (u N).p (u N).d := by
  induction N with
  | zero => exact ⟨fun _ => ⟨w, p, d, 0⟩, rfl, fun k _ h0 => absurd h0 (Nat.not_lt_zero _), h⟩
  | succ N ih =>
    obtain ⟨u, hu0, hus, huN⟩ := ih
    by_cases hN : N < n + m
    · obtain ⟨u', hu', hinv⟩ := clinch_step E I hf c ⟨N, hN⟩ (u N) huN
      refine ⟨fun k => if k ≤ N then u k else u', by simp [hu0], fun k hk hkN => ?_,
        by simpa using hinv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hkN with hlt | heq
      · simp only [if_pos hlt.le, if_pos (show k + 1 ≤ N by omega)]
        exact hus k hk hlt
      · subst heq
        simp only [le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false]
        exact hu'
    · refine ⟨fun k => if k ≤ N then u k else u N, by simp [hu0], fun k hk hkN => ?_,
        by simpa using huN⟩
      have : k < N := by omega
      simp only [if_pos this.le, if_pos (show k + 1 ≤ N by omega)]
      exact hus k hk this

lemma step_exists (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j))
    (ε : ℝ) (hε : 0 < ε) (s : Alg2State E) (h : Inv E I s.c s.w s.p s.d) :
    ∃ s', Alg2Step E I ε s s' ∧ Inv E I s'.c s'.w s'.p s'.d := by
  obtain ⟨u, hu0, hus, huK⟩ := inner_exists E I hf s.c s.w s.p s.d h (n + m)
  refine ⟨⟨(u (n + m)).w, (u (n + m)).p, s.r + (u (n + m)).dr,
      Function.update s.c s.l (s.c s.l + ε),
      Function.update (u (n + m)).d s.l (demandUpdate (extBudget E I s.l) ((u (n + m)).p s.l)
        (Function.update s.c s.l (s.c s.l + ε) s.l) (extBid E I s.l)), finRotate _ s.l⟩,
    ⟨u, hu0, fun k hk => hus k hk hk, rfl, rfl, rfl, rfl, rfl, rfl⟩, huK.1, ?_⟩
  intro k
  by_cases hk : k = s.l
  · subst hk
    simp only [Function.update_self]
    exact invOne_demandUpdate _ _ _ _ (by linarith [(huK.2 s.l).1]) (huK.2 s.l).2.2.1
  · simp only [Function.update_of_ne hk]
    exact huK.2 k

lemma zero_mem_extP (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j)) :
    (0 : ↥(extEdges E) → ℝ) ∈ extP E I := by
  refine ⟨fun _ => le_refl _, fun j => ⟨fun _ _ => le_refl _, fun F hF => ?_⟩⟩
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  obtain ⟨h0, hmono, -⟩ := hf j
  unfold extF
  split_ifs
  · rw [← h0]; exact hmono _ _ (Finset.empty_subset _) (subset_refl _)
  · rw [← h0]
    refine hmono _ _ (Finset.empty_subset _) ?_
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    have := hF he
    simp [extEdgesOfSeller, edgesOfSeller, liftEdge] at this ⊢
    exact this

lemma extBudget_nonneg (I : PublicInfo E) (hB : ∀ i, 0 ≤ I.budget i) (k : Fin (n + m)) :
    (0 : WithTop ℝ) ≤ extBudget E I k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [extBudget, hB i]
  · simp [extBudget]

lemma run_exists (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j))
    (hB : ∀ i, 0 ≤ I.budget i) (ε : ℝ) (hε : 0 < ε) (hK : 0 < n + m) :
    ∃ s : ℕ → Alg2State E, Alg2Init E (s 0) ∧
      ∀ t, Alg2Step E I ε (s t) (s (t + 1)) ∧ Inv E I (s t).c (s t).w (s t).p (s t).d := by
  let P := fun st : Alg2State E => Inv E I st.c st.w st.p st.d
  have hstep : ∀ st : {st // P st}, ∃ st' : {st // P st}, Alg2Step E I ε st.1 st'.1 :=
    fun st => by
      obtain ⟨s', h1, h2⟩ := step_exists E I hf ε hε st.1 st.2
      exact ⟨⟨s', h2⟩, h1⟩
  choose g hg using hstep
  let s0 : Alg2State E := ⟨0, 0, 0, 0, fun _ => ⊤, ⟨0, hK⟩⟩
  have hs0 : P s0 := by
    refine ⟨zero_mem_extP E I hf, fun k => ⟨le_refl _, le_top, ?_, fun r hr => ?_,
      fun _ => Or.inl rfl, fun _ h => absurd h (lt_irrefl 0)⟩⟩
    · simpa [s0] using extBudget_nonneg E I hB k
    · simp [s0] at hr
  refine ⟨fun t => (g^[t] ⟨s0, hs0⟩).1, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun t => ⟨?_, (g^[t] ⟨s0, hs0⟩).2⟩⟩
  simp only [Function.iterate_succ_apply']
  exact hg _

lemma finRotate_val : ∀ (N : ℕ) (x : Fin N), ((finRotate N x : Fin N) : ℕ) = ((x : ℕ) + 1) % N
  | 0, x => x.elim0
  | N + 1, x => by
    rw [finRotate_apply, Fin.val_add]
    rcases N with _ | N
    · simp
    · simp

lemma liftEdge_inj : Function.Injective (liftEdge E) := by
  intro a b h
  have h1 := congrArg (fun x : ↥(extEdges E) => x.1) h
  simp only [liftEdge, Prod.mk.injEq] at h1
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.castAdd_inj.mp h1.1
  · exact h1.2

lemma feasible_toOriginal (I : PublicInfo E) (S : Alg2State E) (h : Inv E I S.c S.w S.p S.d) :
    Feasible E I (toOriginal E S) := by
  obtain ⟨⟨hw0, hwP⟩, hk⟩ := h
  refine ⟨fun e => hw0 _, fun j => ⟨fun e _ => hw0 _, fun F hF => ?_⟩, fun i => ?_⟩
  · have hsub : F.map ⟨liftEdge E, liftEdge_inj E⟩ ⊆ extEdgesOfSeller E j := by
      intro x hx
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have := hF ha
      simp [extEdgesOfSeller, edgesOfSeller, liftEdge] at this ⊢
      exact this
    have h1 := (hwP j).2 _ hsub
    rw [Finset.sum_map] at h1
    have hv : virtEdge E j ∉ F.map ⟨liftEdge E, liftEdge_inj E⟩ := by
      intro hx
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
      obtain ⟨a, -, ha⟩ := hx
      have h2 := congrArg (fun x : ↥(extEdges E) => (x.1.1 : ℕ)) ha
      simp [liftEdge, virtEdge] at h2
      have := a.1.1.isLt
      omega
    have h3 : extF E I j (F.map ⟨liftEdge E, liftEdge_inj E⟩) = I.f j F := by
      unfold extF
      rw [if_neg hv]
      congr 1
      ext e
      simp
    rw [h3] at h1
    exact h1
  · have := (hk (Fin.castAdd m i)).2.2.1
    simpa [extBudget, toOriginal] using this

lemma outcome_exists (ε : ℝ) (hε : 0 < ε) (I : PublicInfo E) (hI : Valid E ε I)
    (hK : 0 < n + m) : ∃ A, Mech2Outcome E I ε A ∧ Feasible E I A := by
  obtain ⟨-, hB, -, hf⟩ := hI
  obtain ⟨s, hinit, hs⟩ := run_exists E I hf hB ε hε hK
  have hl : ∀ t, ((s t).l : ℕ) = t % (n + m) := by
    intro t
    induction t with
    | zero => rw [hinit.2.2.2.2.2]; simp
    | succ t ih =>
      obtain ⟨u, -, -, -, -, -, -, -, hl'⟩ := (hs t).1
      rw [hl', finRotate_val, ih, Nat.mod_add_mod]
  have hc : ∀ t, (s (t + 1)).c = Function.update (s t).c (s t).l ((s t).c (s t).l + ε) := by
    intro t
    obtain ⟨u, -, -, -, -, -, hc', -, -⟩ := (hs t).1
    exact hc'
  have hmono1 : ∀ k t, (s t).c k ≤ (s (t + 1)).c k := by
    intro k t
    rw [hc t]
    by_cases hk : k = (s t).l
    · subst hk; simp only [Function.update_self]; linarith
    · simp only [Function.update_of_ne hk]; exact le_refl _
  have hmono : ∀ k, Monotone (fun t => (s t).c k) := fun k =>
    monotone_nat_of_le_succ (fun t => hmono1 k t)
  have hhit : ∀ (q : ℕ) (i : Fin (n + m)),
      (s (q * (n + m) + i + 1)).c i = (s (q * (n + m) + i)).c i + ε := by
    intro q i
    have hli : (s (q * (n + m) + i)).l = i := by
      apply Fin.ext
      rw [hl, Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt i.2
    rw [hc, hli, Function.update_self]
  have hlow : ∀ (q : ℕ) (i : Fin (n + m)), ((q : ℝ) + 1) * ε ≤ (s (q * (n + m) + i + 1)).c i := by
    intro q i
    induction q with
    | zero =>
      rw [hhit]
      have := ((hs (0 * (n + m) + i)).2.2 i).1
      simp only [Nat.cast_zero, zero_add, one_mul]
      linarith
    | succ q ih =>
      rw [hhit]
      have hle : q * (n + m) + i + 1 ≤ (q + 1) * (n + m) + i := by
        rw [Nat.succ_mul]; omega
      have := hmono i hle
      simp only at this
      push_cast
      linarith
  set V := ∑ k, |extBid E I k| with hV
  obtain ⟨q, hq⟩ := exists_nat_gt (V / ε)
  have hqV : V < q * ε := by rwa [div_lt_iff₀ hε] at hq
  have hex : ∃ t, ∀ i, (s t).d i = 0 := by
    refine ⟨q * (n + m) + (n + m), fun i => ?_⟩
    have h1 := hlow q i
    have h2 := hmono i (show q * (n + m) + i + 1 ≤ q * (n + m) + (n + m) by omega)
    simp only at h2
    have hv : extBid E I i ≤ V := by
      rw [hV]
      exact (le_abs_self _).trans
        (Finset.single_le_sum (f := fun k => |extBid E I k|) (fun k _ => abs_nonneg _)
          (Finset.mem_univ i))
    have hV0 : 0 ≤ V := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    exact ((hs _).2.2 i).2.2.2.2.2 (by nlinarith) (by nlinarith)
  classical
  refine ⟨toOriginal E (s (Nat.find hex)),
    ⟨s (Nat.find hex), ⟨Nat.find hex, s, hinit, fun t ht => ⟨?_, (hs t).1⟩,
      Nat.find_spec hex, rfl⟩, rfl⟩,
    feasible_toOriginal E I _ (hs _).2⟩
  by_contra hcon
  push Not at hcon
  exact Nat.find_min hex ht hcon

lemma valid_withBid (ε : ℝ) (I : PublicInfo E) (hI : Valid E ε I) (i : Fin n) (b : ℝ)
    (hb : OnGrid ε b) : Valid E ε (withBid E I i b) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  refine ⟨fun k => ?_, h2, h3, h4⟩
  by_cases hk : k = i
  · subst hk; simpa [withBid] using hb
  · simpa [withBid, Function.update_of_ne hk] using h1 k

lemma valid_withBids (ε : ℝ) (I : PublicInfo E) (hI : Valid E ε I) (val : Fin n → ℝ)
    (hval : ∀ i, OnGrid ε (val i)) : Valid E ε (withBids E I val) := by
  obtain ⟨-, h2, h3, h4⟩ := hI
  exact ⟨hval, h2, h3, h4⟩

end PolyClinchThm21Sol

open PolyClinchThm21Sol in
theorem solution (n m : ℕ) (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : Mechanism E, OutputsAllocations E ε M ∧ ICb E ε M ∧ IRb E ε M ∧ IRs E ε M ∧
      SBB E ε M ∧ PO E ε M := by
  classical
  by_cases hK : 0 < n + m
  · let M : Mechanism E := fun I =>
      if h : ∃ A, Mech2Outcome E I ε A ∧ Feasible E I A then h.choose else ⟨0, 0, 0⟩
    have hM : ∀ I, Valid E ε I → Mech2Outcome E I ε (M I) ∧ Feasible E I (M I) := by
      intro I hI
      have h := outcome_exists E ε hε I hI hK
      simp only [M, dif_pos h]
      exact h.choose_spec
    refine ⟨M, fun I hI => (hM I hI).2, ?_, ?_, ?_, ?_, ?_⟩
    · intro I val hI hval i
      exact (corollary_3_10 E ε hε I hI val hval i (M I) _ (hM I hI).1
        (hM _ (valid_withBid E ε I hI i (val i) (hval i))).1).1
    · intro I val hI hval i
      exact (corollary_3_10 E ε hε I hI val hval i (M I) _ (hM I hI).1
        (hM _ (valid_withBid E ε I hI i (val i) (hval i))).1).2
    · intro I hI
      exact proposition_3_8 E ε hε I hI (M I) (hM I hI).1
    · intro I hI
      exact lemma_3_7 E ε hε I hI (M I) (hM I hI).1
    · intro I val hI hval
      exact theorem_3_11 E ε hε I hI val hval _ (hM _ (valid_withBids E ε I hI val hval)).1
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn hm
    refine ⟨fun _ => ⟨0, 0, 0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro I _
      exact ⟨fun e => e.1.1.elim0, fun j => j.elim0, fun i => i.elim0⟩
    · intro I val _ _ i; exact i.elim0
    · intro I val _ _ i; exact i.elim0
    · intro I _ j; exact j.elim0
    · intro I _; simp
    · intro I val _ _ h
      obtain ⟨_, _, _, _, _, h⟩ := h
      rcases h with ⟨i, _⟩ | ⟨j, _⟩
      · exact i.elim0
      · exact j.elim0
