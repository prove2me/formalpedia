-- Prove2me | solution 1 for StochSchedPrec.InForest.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:03:44.38012+00:00
-- url     : https://prove2.me/submissions/eeb87e20-c7bc-48cc-9d48-7502f37b27d4

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham
import Theorems.Thm_StochSchedPrec_InForest_lemma_4_3
import Theorems.Thm_StochSchedPrec_InForest_chain_lower_bound
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest.L44Aux

/-- Length of the overlap of `[c, d)` with `[a, b)`. -/
noncomputable def ov (c d a b : ℝ) : ℝ := max (min d b - max c a) 0

lemma ov_nonneg (c d a b : ℝ) : 0 ≤ ov c d a b := le_max_right _ _

/-- Cumulative processing of `[c, d)` up to time `x`. -/
noncomputable def cum (c d x : ℝ) : ℝ := min (max (x - c) 0) (d - c)

lemma ov_eq_cum {c d a b : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : ov c d a b = cum c d b - cum c d a := by
  unfold ov cum
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma ov_add {c d a b e : ℝ} (hab : a ≤ b) (hbe : b ≤ e) (hcd : c ≤ d) :
    ov c d a e = ov c d a b + ov c d b e := by
  rw [ov_eq_cum (hab.trans hbe) hcd, ov_eq_cum hab hcd, ov_eq_cum hbe hcd]
  ring

lemma ov_mono {c d a b b' : ℝ} (h : b ≤ b') : ov c d a b ≤ ov c d a b' := by
  unfold ov
  exact max_le_max (sub_le_sub_right (min_le_min_left _ h) _) le_rfl

lemma ov_le {c d a b : ℝ} (hcd : c ≤ d) : ov c d a b ≤ d - c := by
  unfold ov
  exact max_le (sub_le_sub (min_le_left _ _) (le_max_left _ _)) (by linarith)

lemma ov_self {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) : ov c d 0 d = d - c := by
  unfold ov
  rw [min_self, max_eq_left hc, max_eq_left (by linarith)]

lemma cover {ι : Type*} (W : Finset ι) (s e : ι → ℝ) (a b : ℝ) (hab : a ≤ b) (k : ℕ)
    (h : ∀ t, a ≤ t → t < b → k ≤ (W.filter fun i => s i ≤ t ∧ t < e i).card) :
    (k : ℝ) * (b - a) ≤ ∑ i ∈ W, ov (s i) (e i) a b := by
  have hI : ∀ i, ∫ t in Set.Ico a b, (Set.Ico (s i) (e i)).indicator (fun _ => (1 : ℝ)) t =
      ov (s i) (e i) a b := by
    intro i
    rw [setIntegral_indicator measurableSet_Ico, setIntegral_const, Set.Ico_inter_Ico,
      Real.volume_real_Ico, smul_eq_mul, mul_one]
    unfold ov
    simp only [max_comm a (s i), min_comm b (e i)]
  have hfin : volume (Set.Ico a b) ≠ ⊤ := by simp
  have hint : ∀ i, IntegrableOn ((Set.Ico (s i) (e i)).indicator (fun _ => (1 : ℝ)))
      (Set.Ico a b) := fun i =>
    (integrableOn_const hfin).indicator measurableSet_Ico
  calc (k : ℝ) * (b - a) = ∫ _ in Set.Ico a b, (k : ℝ) := by
        rw [setIntegral_const, Real.volume_real_Ico_of_le hab, smul_eq_mul, mul_comm]
    _ ≤ ∫ t in Set.Ico a b, ∑ i ∈ W, (Set.Ico (s i) (e i)).indicator (fun _ => (1 : ℝ)) t := by
        refine setIntegral_mono_on (integrableOn_const hfin)
          (integrable_finset_sum _ fun i _ => hint i) measurableSet_Ico fun t ht => ?_
        have hc := h t ht.1 ht.2
        have : ∑ i ∈ W, (Set.Ico (s i) (e i)).indicator (fun _ => (1 : ℝ)) t =
            ((W.filter fun i => s i ≤ t ∧ t < e i).card : ℝ) := by
          simp only [Set.indicator_apply, Set.mem_Ico]
          rw [Finset.sum_boole]
        rw [this]
        exact_mod_cast hc
    _ = ∑ i ∈ W, ∫ t in Set.Ico a b, (Set.Ico (s i) (e i)).indicator (fun _ => (1 : ℝ)) t :=
        integral_finset_sum _ fun i _ => hint i
    _ = ∑ i ∈ W, ov (s i) (e i) a b := Finset.sum_congr rfl fun i _ => hI i

variable {V : Type*} [Fintype V]

lemma availTime_le_iff (A : V → V → Prop) (p S : V → ℝ) (j : V) (c : ℝ) :
    availTime A p S j ≤ c ↔ 0 ≤ c ∧ ∀ i, Relation.TransGen A i j → S i + p i ≤ c := by
  classical
  unfold availTime
  rw [Finset.fold_max_le]
  simp [Finset.mem_filter]

lemma le_availTime (A : V → V → Prop) (p S : V → ℝ) (j i : V) (h : Relation.TransGen A i j) :
    S i + p i ≤ availTime A p S j :=
  ((availTime_le_iff A p S j (availTime A p S j)).mp le_rfl).2 i h

lemma exists_attain (A : V → V → Prop) (p S : V → ℝ) (j : V) (h : 0 < availTime A p S j) :
    ∃ i, Relation.TransGen A i j ∧ S i + p i = availTime A p S j := by
  classical
  have h2 : availTime A p S j ≤ availTime A p S j := le_rfl
  unfold availTime at h2
  rw [Finset.le_fold_max] at h2
  rcases h2 with h2 | ⟨i, hi, hle⟩
  · exact absurd h (not_lt.mpr h2)
  · exact ⟨i, (Finset.mem_filter.mp hi).2,
      le_antisymm (le_availTime A p S j i (Finset.mem_filter.mp hi).2) hle⟩

lemma path_le (A : V → V → Prop) (m : ℕ) (p S : V → ℝ) (hp : IsNonneg p)
    (hS : IsFeasibleSchedule A m p S) {i j : V} (h : Relation.TransGen A i j) :
    S i + p i ≤ S j := by
  induction h with
  | single hab => exact hS.2.1 _ _ hab
  | @tail b c _ hbc ih =>
    have := hS.2.1 _ _ hbc
    have := hp b
    linarith

lemma chainLenAux_nonneg (crit : V → Option V) (p : V → ℝ) (hp : IsNonneg p) (n : ℕ) :
    ∀ j, 0 ≤ chainLenAux crit p n j := by
  induction n with
  | zero => intro j; exact hp j
  | succ n ih =>
    intro j
    simp only [chainLenAux]
    split
    · exact hp j
    · exact add_nonneg (hp j) (ih _)

/-- Deterministic form of Lemma 4.4 (multiplied by `m`). -/
lemma det_bound [DecidableEq V] (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (hforest : IsInForest A)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsLinearExtension A L)
    (p : V → ℝ) (hp : IsNonneg p) (S : V → ℝ) (hS : IsGraham A m L p S)
    (crit : V → Option V) (hcrit : IsCritSelector A p S crit) (j : V) :
    (m : ℝ) * (S j + p j) ≤ ((m : ℝ) - 1) * chainLen crit p j + ∑ i ∈ Bset L j, p i := by
  classical
  have hF := hS.1
  have hgreedy := hS.2.1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let d : V → ℕ := fun x => (Finset.univ.filter fun i => Relation.TransGen A i x).card
  have hd : ∀ y x, Relation.TransGen A y x → d y < d x := by
    intro y x hyx
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨y, by simp [hyx], by simp [hacyc y]⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.trans hyx
  have hdlt : ∀ x, d x < Fintype.card V := by
    intro x
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨x, Finset.mem_univ _, by simp [hacyc x]⟩
  -- busy jobs during a waiting period of `x` lie in `B_x \ {x}`
  have hwait : ∀ x t, availTime A p S x ≤ t → t < S x →
      m ≤ (((Bset L x).erase x).filter fun i => S i ≤ t ∧ t < S i + p i).card := by
    intro x t h1 h2
    have hav : IsAvailable A p S x t :=
      ⟨((availTime_le_iff A p S x _).mp le_rfl).1.trans h1,
        fun i hi => (le_availTime A p S x i hi).trans h1⟩
    refine (hgreedy x t hav h2).trans (Finset.card_le_card ?_)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_filter, Finset.mem_erase, Bset, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, hk⟩
    · rintro rfl; linarith [hk.1]
    · by_contra hlt
      push_neg at hlt
      exact lemma_4_3 m hm A hacyc hforest L hL p hp S hS x k
        (by simp [Aset, hlt]) t h1 h2 hk
  -- the inductive invariant
  have key : ∀ n, ∀ x, d x < n →
      (m : ℝ) * (S x + p x) ≤ ((m : ℝ) - 1) * chainLenAux crit p n x +
        ∑ i ∈ Bset L x, ov (S i) (S i + p i) 0 (S x + p x) := by
    intro n
    induction n with
    | zero => intro x hx; omega
    | succ n ih =>
      intro x hx
      have hxB : x ∈ Bset L x := by simp [Bset]
      have hsplit : ∑ i ∈ Bset L x, ov (S i) (S i + p i) 0 (S x + p x) =
          ov (S x) (S x + p x) 0 (S x + p x) +
            ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S x + p x) :=
        (Finset.add_sum_erase _ _ hxB).symm
      have hself : ov (S x) (S x + p x) 0 (S x + p x) = p x := by
        rw [ov_self (hF.1 x) (by linarith [hp x])]; ring
      have hSx0 := hF.1 x
      have hpx := hp x
      cases hc : crit x with
      | none =>
        have hr : availTime A p S x = 0 := by
          by_contra hne
          have hpos : 0 < availTime A p S x :=
            lt_of_le_of_ne ((availTime_le_iff A p S x _).mp le_rfl).1 (Ne.symm hne)
          obtain ⟨i, hi, hieq⟩ := exists_attain A p S x hpos
          apply (hcrit x).2 hc
          exact ⟨i, hi, by rw [hieq]; exact hpos, fun i' hi' => hieq ▸ le_availTime A p S x i' hi'⟩
        have hcov := cover ((Bset L x).erase x) S (fun i => S i + p i) 0 (S x) hSx0 m
          (fun t ht1 ht2 => hwait x t (hr ▸ ht1) ht2)
        have hmono : ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S x) ≤
            ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S x + p x) :=
          Finset.sum_le_sum fun i _ => ov_mono (by linarith)
        simp only [chainLenAux, hc]
        rw [hsplit, hself]
        nlinarith
      | some y =>
        obtain ⟨hyx, hy0, hymax⟩ := (hcrit x).1 y hc
        have hry : availTime A p S x = S y + p y := le_antisymm
          ((availTime_le_iff A p S x _).mpr ⟨hy0.le, hymax⟩) (le_availTime A p S x y hyx)
        have hdy : d y < n := by have := hd y x hyx; omega
        have hIH := ih y hdy
        have hyS : S y + p y ≤ S x := path_le A m p S hp hF hyx
        have hcov := cover ((Bset L x).erase x) S (fun i => S i + p i) (S y + p y) (S x) hyS m
          (fun t ht1 ht2 => hwait x t (hry ▸ ht1) ht2)
        have hsubB : Bset L y ⊆ (Bset L x).erase x := by
          intro i hi
          have hlt := hL y x hyx
          simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
          refine ⟨?_, hi.trans hlt.le⟩
          rintro rfl; exact absurd hlt (not_lt.mpr hi)
        have h1 : ∑ i ∈ Bset L y, ov (S i) (S i + p i) 0 (S y + p y) ≤
            ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S y + p y) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubB fun i _ _ => ov_nonneg _ _ _ _
        have h2 : ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S y + p y) +
            ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) (S y + p y) (S x) ≤
            ∑ i ∈ (Bset L x).erase x, ov (S i) (S i + p i) 0 (S x + p x) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← ov_add hy0.le hyS (by linarith [hp i])]
          exact ov_mono (by linarith)
        simp only [chainLenAux, hc]
        rw [hsplit, hself]
        nlinarith
  have := key (Fintype.card V) j (hdlt j)
  have hle : ∑ i ∈ Bset L j, ov (S i) (S i + p i) 0 (S j + p j) ≤ ∑ i ∈ Bset L j, p i :=
    Finset.sum_le_sum fun i _ => by
      have := ov_le (c := S i) (d := S i + p i) (a := 0) (b := S j + p j) (by linarith [hp i])
      linarith
  unfold chainLen
  linarith

end StochSchedPrec.InForest.L44Aux

open StochSchedPrec.InForest StochSchedPrec.InForest.L44Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (hPint : ∀ j, Integrable (P j) Pr)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsLinearExtension A L)
    (γ : (V → ℝ) → (V → ℝ)) (hγ : ∀ p, IsNonneg p → IsGraham A m L p (γ p))
    (hγmeas : ∀ j, AEMeasurable (fun ω => γ (fun k => P k ω) j) Pr)
    (crit : (V → ℝ) → V → Option V) (hcrit : ∀ p, IsNonneg p → IsCritSelector A p (γ p) (crit p))
    (hℓmeas : ∀ j, AEMeasurable
      (fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j) Pr)
    (j : V) :
    ∫ ω, (γ (fun k => P k ω) j + P j ω) ∂Pr ≤
      ((m : ℝ) - 1) / m * ∫ ω, chainLen (crit (fun k => P k ω)) (fun k => P k ω) j ∂Pr
        + 1 / (m : ℝ) * ∑ i ∈ Bset L j, ∫ ω, P i ω ∂Pr := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hnn : ∀ ω, IsNonneg (fun k => P k ω) := fun ω k => hP.2.1 k ω
  set ℓ : Ω → ℝ := fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j with hℓ
  set Cg : Ω → ℝ := fun ω => γ (fun k => P k ω) j + P j ω with hCg
  have hℓ0 : ∀ ω, 0 ≤ ℓ ω := fun ω =>
    chainLenAux_nonneg _ _ (hnn ω) _ j
  have hℓC : ∀ ω, ℓ ω ≤ Cg ω := fun ω =>
    (chain_lower_bound m hm A hacyc P hP hPint γ (fun p hp => (hγ p hp).1) crit hcrit
      hℓmeas).1 _ (hnn ω) _ (hγ _ (hnn ω)).1 j
  have hpt : ∀ ω, Cg ω ≤ ((m : ℝ) - 1) / m * ℓ ω + 1 / (m : ℝ) * ∑ i ∈ Bset L j, P i ω := by
    intro ω
    have h := det_bound m hm A hacyc hforest L hL _ (hnn ω) _ (hγ _ (hnn ω)) _
      (hcrit _ (hnn ω)) j
    have e1 : ((m : ℝ) - 1) / m * ℓ ω + 1 / (m : ℝ) * ∑ i ∈ Bset L j, P i ω =
        (((m : ℝ) - 1) * ℓ ω + ∑ i ∈ Bset L j, P i ω) / m := by
      field_simp
    rw [e1, le_div_iff₀ hmpos]
    simp only [hCg, hℓ]
    linarith
  have hRHS0 : 0 ≤ ((m : ℝ) - 1) / m * ∫ ω, ℓ ω ∂Pr
      + 1 / (m : ℝ) * ∑ i ∈ Bset L j, ∫ ω, P i ω ∂Pr := by
    apply add_nonneg
    · exact mul_nonneg (div_nonneg (by linarith) hmpos.le) (integral_nonneg hℓ0)
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
        integral_nonneg fun ω => hP.2.1 i ω)
  by_cases hint : Integrable Cg Pr
  · have hℓint : Integrable ℓ Pr := hint.mono' (hℓmeas j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hℓ0 ω)]; exact hℓC ω)
    have hsumint : Integrable (fun ω => ∑ i ∈ Bset L j, P i ω) Pr :=
      integrable_finset_sum _ fun i _ => hPint i
    calc ∫ ω, Cg ω ∂Pr
        ≤ ∫ ω, (((m : ℝ) - 1) / m * ℓ ω + 1 / (m : ℝ) * ∑ i ∈ Bset L j, P i ω) ∂Pr :=
          integral_mono hint ((hℓint.const_mul _).add (hsumint.const_mul _)) hpt
      _ = ((m : ℝ) - 1) / m * ∫ ω, ℓ ω ∂Pr
            + 1 / (m : ℝ) * ∑ i ∈ Bset L j, ∫ ω, P i ω ∂Pr := by
          rw [integral_add (hℓint.const_mul _) (hsumint.const_mul _), integral_const_mul,
            integral_const_mul, integral_finset_sum _ fun i _ => hPint i]
  · rw [integral_undef hint]
    exact hRHS0
