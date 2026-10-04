-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.sufficiency_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:34:03.05016+00:00
-- url     : https://prove2.me/submissions/9f51a4b6-fb5a-4790-b52f-e6c3d538ca2d

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation

set_option autoImplicit false

open Finset in
lemma e65_hoeff_count {l : ℕ} (hl : 1 ≤ l) (c : Fin l → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ)
      ≤ (2 : ℝ) ^ l * Real.exp (-(t ^ 2 / (2 * l))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  set lam : ℝ := t / l with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht hlpos.le
  have hmark : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases h : t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i
    · simp only [h, if_true, Nat.cast_one, one_mul]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam0)
    · simp only [h, if_false, Nat.cast_zero, zero_mul]
      exact (Real.exp_pos _).le
  have hprod : ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
      = ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i))) := by
    have h1 : ∀ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
        = ∏ i : Fin l, Real.exp (lam * ((if s i then (1 : ℝ) else -1) * c i)) := by
      intro s
      rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [h1]
    have := Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset Bool))
      (fun i b => Real.exp (lam * ((if b then (1 : ℝ) else -1) * c i)))
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg]
  have hfac : ∀ i : Fin l, Real.exp (lam * c i) + Real.exp (-(lam * c i))
      ≤ 2 * Real.exp (lam ^ 2 / 2) := by
    intro i
    have h1 := Real.cosh_le_exp_half_sq (lam * c i)
    rw [Real.cosh_eq] at h1
    have h2 : (lam * c i) ^ 2 ≤ lam ^ 2 := by
      have : |lam * c i| ≤ lam := by
        rw [abs_mul, abs_of_nonneg hlam0]
        calc lam * |c i| ≤ lam * 1 := mul_le_mul_of_nonneg_left (hc i) hlam0
          _ = lam := mul_one _
      have h3 := sq_le_sq' (by linarith [abs_nonneg (lam * c i), neg_abs_le (lam * c i)] : -lam ≤ lam * c i)
        (le_trans (le_abs_self _) this)
      exact h3
    have h4 : Real.exp ((lam * c i) ^ 2 / 2) ≤ Real.exp (lam ^ 2 / 2) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  have hprod2 : ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i)))
      ≤ (2 * Real.exp (lam ^ 2 / 2)) ^ l := by
    calc _ ≤ ∏ _i : Fin l, (2 * Real.exp (lam ^ 2 / 2)) :=
          Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfac i)
      _ = _ := by simp
  have hexp : Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))) = Real.exp (lam ^ 2 / 2 * l) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlam]
    field_simp
    ring
  have hpow : (2 * Real.exp (lam ^ 2 / 2)) ^ l = 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hcount : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [← hpow]; rw [hprod] at hmark; exact hmark.trans hprod2
  rw [← hexp] at hcount
  have hpos : 0 < Real.exp (lam * t) := Real.exp_pos _
  have := hcount
  rw [show (2 : ℝ) ^ l * (Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))))
      = (2 ^ l * Real.exp (-(t ^ 2 / (2 * l)))) * Real.exp (lam * t) by ring] at this
  exact le_of_mul_le_mul_right this hpos


/-- Swap the two halves at the positions where `τ` is `true`. -/
def e65SwS (l : ℕ) (τ : Fin l → Bool) : Fin l ⊕ Fin l → Fin l ⊕ Fin l
  | Sum.inl i => if τ i then Sum.inr i else Sum.inl i
  | Sum.inr i => if τ i then Sum.inl i else Sum.inr i

lemma e65SwS_inv (l : ℕ) (τ : Fin l → Bool) : Function.Involutive (e65SwS l τ) := by
  intro a
  cases a with
  | inl i => by_cases h : τ i <;> simp [e65SwS, h]
  | inr i => by_cases h : τ i <;> simp [e65SwS, h]

def e65Sw (l : ℕ) (τ : Fin l → Bool) : Equiv.Perm (Fin (l + l)) :=
  (finSumFinEquiv.symm.trans (Function.Involutive.toPerm _ (e65SwS_inv l τ))).trans finSumFinEquiv

lemma e65Sw_castAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    e65Sw l τ (Fin.castAdd l i) = if τ i then Fin.natAdd l i else Fin.castAdd l i := by
  by_cases h : τ i <;> simp [e65Sw, e65SwS, h]

lemma e65Sw_natAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    e65Sw l τ (Fin.natAdd l i) = if τ i then Fin.castAdd l i else Fin.natAdd l i := by
  simp only [e65Sw, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Function.Involutive.coe_toPerm, e65SwS]
  by_cases h : τ i <;> simp only [h, if_true, Bool.false_eq_true, if_false, ↓reduceIte,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

open VapnikChervonenkis.Shared in
lemma e65_sup_attained {X : Type*} (S : Set (Set X)) (l : ℕ) (z : Fin (l + l) → X) {r : ℝ}
    (hr : 0 < r) (h : r ≤ semiSampleDeviation S l z) :
    ∃ A ∈ S, r ≤ |relFreq A (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq A (fun i : Fin l => z (Fin.natAdd l i))| := by
  classical
  unfold semiSampleDeviation at h
  set f : S → ℝ := fun A => |relFreq (A : Set X) (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq (A : Set X) (fun i : Fin l => z (Fin.natAdd l i))| with hf
  by_cases hne : Nonempty S
  · set F : Finset (Fin (l + l)) → ℝ := fun t =>
      |((Finset.univ.filter (fun i : Fin l => Fin.castAdd l i ∈ t)).card : ℝ) / l
        - ((Finset.univ.filter (fun i : Fin l => Fin.natAdd l i ∈ t)).card : ℝ) / l| with hF
    have hfF : ∀ A : S, f A = F (Finset.univ.filter (fun j => z j ∈ (A : Set X))) := by
      intro A
      simp only [hf, hF, relFreq, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfin : (Set.range f).Finite := by
      refine (Set.finite_range F).subset ?_
      rintro _ ⟨A, rfl⟩
      exact ⟨_, (hfF A).symm⟩
    have hmem := Set.Nonempty.csSup_mem (Set.range_nonempty f) hfin
    obtain ⟨A, hA⟩ := hmem
    refine ⟨A, A.2, ?_⟩
    have : r ≤ f A := by rw [hA]; exact h
    exact this
  · rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at h
    linarith

open VapnikChervonenkis.Shared in
lemma e65_count {X : Type*} (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l) {ε : ℝ} (hε : 0 < ε)
    (y : Fin (l + l) → X) :
    ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ e65Sw l τ)).card : ℝ)
      ≤ (index S y : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  set T : Finset (Finset (Fin (l + l))) :=
    Finset.univ.filter (fun t : Finset (Fin (l + l)) => ∃ A ∈ S, ∀ i, i ∈ t ↔ y i ∈ A) with hT
  have hTcard : T.card = index S y := by
    unfold index
    first | rfl | congr
  set c : Finset (Fin (l + l)) → Fin l → ℝ := fun t i =>
    (if Fin.castAdd l i ∈ t then (1 : ℝ) else 0) - (if Fin.natAdd l i ∈ t then (1 : ℝ) else 0)
    with hc
  have hc1 : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    simp only [hc]
    rw [abs_le]
    by_cases h1 : Fin.castAdd l i ∈ t <;> by_cases h2 : Fin.natAdd l i ∈ t <;>
      simp only [h1, h2, if_true, if_false, ↓reduceIte] <;> norm_num
  set Bad : Finset (Fin (l + l)) → Finset (Fin l → Bool) := fun t =>
    Finset.univ.filter (fun σ : Fin l → Bool =>
      (l : ℝ) * (ε / 2) ≤ |∑ i, (if σ i then (1 : ℝ) else -1) * c t i|) with hBad
  have hBadcard : ∀ t, ((Bad t).card : ℝ) ≤ 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) := by
    intro t
    have hexp : (l * (ε / 2)) ^ 2 / (2 * (l : ℝ)) = ε ^ 2 * l / 8 := by
      field_simp; ring
    have hnn : 0 ≤ (l : ℝ) * (ε / 2) := by positivity
    have h1 := e65_hoeff_count hl1 (c t) (hc1 t) hnn
    have h2 := e65_hoeff_count hl1 (fun i => - c t i)
      (fun i => by simpa [abs_neg] using hc1 t i) hnn
    beta_reduce at h2
    rw [hexp] at h1 h2
    have hsub : Bad t ⊆
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c t i) ∪
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * (- c t i)) := by
      intro σ hσ
      simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hσ ⊢
      have hneg : ∑ i, (if σ i then (1 : ℝ) else -1) * (- c t i)
          = - ∑ i, (if σ i then (1 : ℝ) else -1) * c t i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hneg]
      rcases le_abs'.1 hσ with h | h
      · right; linarith
      · left; linarith
    have := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    push_cast at this
    linarith
  have hsubset : (Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ e65Sw l τ)) ⊆ T.biUnion Bad := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨A, hAS, hA⟩ := e65_sup_attained S l (y ∘ e65Sw l σ) (by positivity) hσ
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A), ?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, hAS, fun i => by simp⟩
    · simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
      set tA : Finset (Fin (l + l)) := Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A)
        with htA
      have hci : ∀ i : Fin l, c tA i
          = (if y (Fin.castAdd l i) ∈ A then (1 : ℝ) else 0)
            - (if y (Fin.natAdd l i) ∈ A then (1 : ℝ) else 0) := by
        intro i
        simp only [hc, htA, Finset.mem_filter, Finset.mem_univ, true_and]
      have hdiff : relFreq A (fun i : Fin l => (y ∘ e65Sw l σ) (Fin.castAdd l i))
          - relFreq A (fun i : Fin l => (y ∘ e65Sw l σ) (Fin.natAdd l i))
          = - (∑ i, (if σ i then (1 : ℝ) else -1) * c tA i) / l := by
        unfold relFreq
        rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← sub_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hci i]
        simp only [Function.comp_apply, e65Sw_castAdd, e65Sw_natAdd]
        by_cases h : σ i <;> by_cases h1 : y (Fin.castAdd l i) ∈ A <;>
          by_cases h2 : y (Fin.natAdd l i) ∈ A <;>
          simp only [h, h1, h2, if_true, if_false, Bool.false_eq_true, ↓reduceIte] <;> norm_num
      rw [hdiff, abs_div, abs_neg, abs_of_pos hlpos, le_div_iff₀ hlpos] at hA
      linarith
  have hcard1 := Finset.card_le_card hsubset
  have hcard2 := hcard1.trans Finset.card_biUnion_le
  have hcard3 : ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ e65Sw l τ)).card : ℝ)
      ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := by
    exact_mod_cast hcard2
  calc _ ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := hcard3
    _ ≤ ∑ _t ∈ T, 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) :=
        Finset.sum_le_sum fun t _ => hBadcard t
    _ = (T.card : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hTcard]

open VapnikChervonenkis.Shared in
lemma e65_index_perm {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X)
    (σ : Equiv.Perm (Fin r)) : index S (x ∘ σ) = index S x := by
  classical
  unfold index
  refine Finset.card_equiv (Equiv.finsetCongr σ) ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun j => ?_⟩
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv, ht]
    simp
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun i => ?_⟩
    have := ht (σ i)
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv] at this
    simpa using this


open MeasureTheory in
lemma e07_comp_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun y : Fin n → X => y ∘ σ)
      (Measure.pi fun _ : Fin n => P) (Measure.pi fun _ : Fin n => P) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => P) σ.symm
  convert h using 1
  funext y b
  rw [MeasurableEquiv.coe_piCongrLeft]
  conv_rhs => rw [← σ.symm_apply_apply b]
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

open MeasureTheory in
lemma e07_avg {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (l : ℕ) (B : Set (Fin (l + l) → X)) (hB : MeasurableSet B) (M : ℝ)
    [∀ y : Fin (l + l) → X, DecidablePred fun τ : Fin l → Bool => y ∘ e65Sw l τ ∈ B]
    (hM : ∀ y : Fin (l + l) → X,
      ((Finset.univ.filter fun τ : Fin l → Bool => y ∘ e65Sw l τ ∈ B).card : ℝ) ≤ M) :
    (Measure.pi fun _ : Fin (l + l) => P) B ≤ ENNReal.ofReal (M / 2 ^ l) := by
  set μ := Measure.pi fun _ : Fin (l + l) => P with hμ
  have hm : ∀ τ : Fin l → Bool, Measurable (fun y : Fin (l + l) → X => y ∘ e65Sw l τ) :=
    fun τ => (e07_comp_mp P (e65Sw l τ)).measurable
  have h1 : ∀ τ : Fin l → Bool,
      μ ((fun y : Fin (l + l) → X => y ∘ e65Sw l τ) ⁻¹' B) = μ B :=
    fun τ => (e07_comp_mp P (e65Sw l τ)).measure_preimage hB.nullMeasurableSet
  have hsum : ∫⁻ y, ((Finset.univ.filter fun τ : Fin l → Bool =>
        y ∘ e65Sw l τ ∈ B).card : ENNReal) ∂μ = ∑ _τ : Fin l → Bool, μ B := by
    have : ∀ y : Fin (l + l) → X, ((Finset.univ.filter fun τ : Fin l → Bool =>
        y ∘ e65Sw l τ ∈ B).card : ENNReal)
        = ∑ τ : Fin l → Bool, ((fun y : Fin (l + l) → X => y ∘ e65Sw l τ) ⁻¹' B).indicator
            (fun _ => (1 : ENNReal)) y := by
      intro y
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases h : y ∘ e65Sw l τ ∈ B <;> simp [Set.indicator_apply, h]
    simp_rw [this]
    rw [lintegral_finsetSum _ (fun τ _ => measurable_const.indicator ((hm τ) hB))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lintegral_indicator_const ((hm τ) hB), one_mul, h1 τ]
  have hint : ∫⁻ y, ((Finset.univ.filter fun τ : Fin l → Bool =>
        y ∘ e65Sw l τ ∈ B).card : ENNReal) ∂μ ≤ ENNReal.ofReal M := by
    calc _ ≤ ∫⁻ _y, ENNReal.ofReal M ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (hM y)
      _ = ENNReal.ofReal M := by simp
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hint
  have h2 : ENNReal.ofReal (M / 2 ^ l) = ENNReal.ofReal M / 2 ^ l := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [h2, ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm]
  push_cast at hint
  exact hint

open MeasureTheory VapnikChervonenkis in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 1 ≤ l) :
    (Measure.pi (fun _ : Fin (l + l) => P)).real {x | ε / 2 ≤ Shared.semiSampleDeviation S l x}
      ≤ 2 * (2 / Real.exp 1) ^ (ε ^ 2 * l / 8)
        + (Measure.pi (fun _ : Fin (l + l) => P)).real
            {x | ε ^ 2 / 16 < Real.logb 2 (Shared.index S x : ℝ) / (2 * (l : ℝ))} := by
  classical
  set μ := Measure.pi (fun _ : Fin (l + l) => P) with hμ
  set C := {x : Fin (l + l) → X | ε / 2 ≤ Shared.semiSampleDeviation S l x} with hC
  set D := {x : Fin (l + l) → X |
    ε ^ 2 / 16 < Real.logb 2 (Shared.index S x : ℝ) / (2 * (l : ℝ))} with hD
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hCm : MeasurableSet C := measurableSet_le measurable_const (hρ l)
  have hDm : MeasurableSet D := by
    refine measurableSet_lt measurable_const ?_
    refine Measurable.div_const ?_ _
    have h1 : Measurable (fun x : Fin (l + l) → X => (Shared.index S x : ℝ)) :=
      (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (hΔ (l + l))
    unfold Real.logb
    exact (Real.measurable_log.comp h1).div_const _
  have hidx : ∀ y : Fin (l + l) → X, y ∉ D →
      (Shared.index S y : ℝ) ≤ (2 : ℝ) ^ (ε ^ 2 * l / 8) := by
    intro y hy
    simp only [hD, Set.mem_setOf_eq, not_lt] at hy
    rcases Nat.eq_zero_or_pos (Shared.index S y) with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero]; positivity
    · have hpos : (0 : ℝ) < Shared.index S y := by exact_mod_cast h0
      have : Real.logb 2 (Shared.index S y) ≤ ε ^ 2 * l / 8 := by
        rw [div_le_iff₀ (by positivity)] at hy
        nlinarith
      exact (Real.logb_le_iff_le_rpow (by norm_num) hpos).1 this
  have hcount : ∀ y : Fin (l + l) → X,
      ((Finset.univ.filter fun τ : Fin l → Bool => y ∘ e65Sw l τ ∈ C ∩ Dᶜ).card : ℝ)
        ≤ (2 : ℝ) ^ (ε ^ 2 * l / 8) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
    intro y
    by_cases hex : ∃ τ : Fin l → Bool, y ∘ e65Sw l τ ∈ C ∩ Dᶜ
    · obtain ⟨τ0, hτ0⟩ := hex
      have hyD : (Shared.index S y : ℝ) ≤ (2 : ℝ) ^ (ε ^ 2 * l / 8) := by
        have := hidx _ hτ0.2
        rwa [e65_index_perm] at this
      have hsub : (Finset.univ.filter fun τ : Fin l → Bool => y ∘ e65Sw l τ ∈ C ∩ Dᶜ) ⊆
          (Finset.univ.filter fun τ : Fin l → Bool =>
            ε / 2 ≤ Shared.semiSampleDeviation S l (y ∘ e65Sw l τ)) := by
        intro τ hτ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        exact hτ.1
      calc _ ≤ ((Finset.univ.filter fun τ : Fin l → Bool =>
            ε / 2 ≤ Shared.semiSampleDeviation S l (y ∘ e65Sw l τ)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := e65_count S l hl hε y
        _ ≤ _ := by gcongr
    · push_neg at hex
      have : (Finset.univ.filter fun τ : Fin l → Bool => y ∘ e65Sw l τ ∈ C ∩ Dᶜ) = ∅ := by
        ext τ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact hex τ
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
  have hB := e07_avg P l (C ∩ Dᶜ) (hCm.inter hDm.compl) _ hcount
  have hMeq : (2 : ℝ) ^ (ε ^ 2 * l / 8) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))))
      / 2 ^ l = 2 * (2 / Real.exp 1) ^ (ε ^ 2 * l / 8) := by
    rw [Real.div_rpow (by norm_num) (Real.exp_pos 1).le, Real.exp_one_rpow, Real.exp_neg]
    field_simp
  rw [hMeq] at hB
  have hB' : μ.real (C ∩ Dᶜ) ≤ 2 * (2 / Real.exp 1) ^ (ε ^ 2 * l / 8) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hB
  have hsub : C ⊆ (C ∩ Dᶜ) ∪ D := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · exact Or.inl ⟨hx, hxD⟩
  calc μ.real C ≤ μ.real ((C ∩ Dᶜ) ∪ D) := measureReal_mono hsub
    _ ≤ μ.real (C ∩ Dᶜ) + μ.real D := measureReal_union_le _ _
    _ ≤ _ := by linarith
