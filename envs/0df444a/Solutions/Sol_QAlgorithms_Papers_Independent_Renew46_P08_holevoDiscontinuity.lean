-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P08.holevoDiscontinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:26:08.145268+00:00
-- url     : https://prove2.me/submissions/597781c6-198b-414c-8ccf-3840883a06e5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsTraceClass)

def g66a_e {I : Type} (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

lemma g66a_e_apply {I : Type} (i a : I) : g66a_e i a = if a = i then 1 else 0 := by
  simp [g66a_e, lp.single_apply, Pi.single_apply]

lemma g66a_e_norm {I : Type} (i : I) : ‖g66a_e i‖ = 1 := by
  simp [g66a_e, lp.norm_single (p := 2) (by norm_num)]

def g66a_exp2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) : NuclearExpansion X where
  left n := if n = 0 then u else if n = 1 then u' else 0
  right n := if n = 0 then v else if n = 1 then v' else 0
  summable := by
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [h0, h1]
  coefficients i j := by
    rw [hX, tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      simp [h0, h1]

lemma g66a_ts2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) :
    traceSize X ≤ ENNReal.ofReal (‖u‖ * ‖v‖ + ‖u'‖ * ‖v'‖) := by
  refine (iInf_le _ (g66a_exp2 X u v u' v' hX)).trans (le_of_eq ?_)
  congr 1
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [g66a_exp2, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [g66a_exp2, h0, h1]

def g66a_P {I : Type} (i : I) : Matrix I I ℂ := fun a b => g66a_e i a * star (g66a_e i b)

lemma g66a_P_apply {I : Type} (i a b : I) : g66a_P i a b = if a = i ∧ b = i then 1 else 0 := by
  simp only [g66a_P, g66a_e_apply]
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]

lemma g66a_P_density {I : Type} (i : I) : IsDensity (g66a_P i) := by
  refine ⟨⟨g66a_exp2 _ (g66a_e i) (g66a_e i) 0 0 (fun a b => by simp [g66a_P])⟩, ?_, ?_, ?_⟩
  · intro s z
    have : (∑ a ∈ s, ∑ b ∈ s, star (z a) * g66a_P i a b * z b) =
        star (∑ b ∈ s, star (g66a_e i b) * z b) * (∑ b ∈ s, star (g66a_e i b) * z b) := by
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      simp only [g66a_P, star_mul, star_star]
      ring
    rw [this]
    set S := ∑ b ∈ s, star (g66a_e i b) * z b
    have h := Complex.conj_mul' S
    rw [show star S = (starRingEnd ℂ) S from rfl, h]
    constructor
    · norm_cast
    · norm_cast; positivity
  · apply summable_of_ne_finset_zero (s := {i})
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simp [g66a_P_apply, ha]
  · rw [tsum_eq_single i]
    · simp [g66a_P_apply]
    · intro a ha; simp [g66a_P_apply, ha]

def g66a_pure {I : Type} (i : I) : State I := ⟨g66a_P i, g66a_P_density i⟩
open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy)

lemma g66a_relent_self {I : Type} (A : Matrix I I ℂ) : extendedRelativeEntropyNats A A = 0 := by
  unfold extendedRelativeEntropyNats
  refine le_antisymm (iSup_le fun s => ?_) bot_le
  unfold finiteRelativeEntropy
  simp

lemma g66a_fre_one {F : Type} [Fintype F] [DecidableEq F] [Subsingleton F] [Nonempty F]
    (A B : Matrix F F ℂ) (w : ℝ) (hw : 0 < w) (hA : ∀ a, A a a = 1) (hB : ∀ a, B a a = w) :
    finiteRelativeEntropy A B = ENNReal.ofReal (-Real.log w + w - 1) := by
  have hA1 : A = 1 := by
    ext a b; rw [Subsingleton.elim b a, hA]; simp
  have hB1 : B = algebraMap ℝ (Matrix F F ℂ) w := by
    ext a b; rw [Subsingleton.elim b a, hB]; simp [Matrix.algebraMap_matrix_apply]
  have hcard : Fintype.card F = 1 := Fintype.card_eq_one_iff.mpr
    ⟨Classical.arbitrary F, fun a => Subsingleton.elim _ _⟩
  unfold finiteRelativeEntropy
  rw [if_pos]
  · rw [hA1, hB1, cfc_algebraMap, cfc_apply_one (R := ℝ)]
    simp only [Real.log_one, map_zero, mul_zero, one_mul, zero_sub]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, hcard]
  · intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [hB1, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    have : v = 0 := by
      have hw' : (w : ℝ) ≠ 0 := hw.ne'
      exact (smul_eq_zero.mp hv).resolve_left hw'
    simp [this]

lemma g66a_relent_single {I : Type} (x : I) (A B : Matrix I I ℂ) (w : ℝ) (hw : 0 < w)
    (hA : A x x = 1) (hB : B x x = w) :
    ENNReal.ofReal (-Real.log w + w - 1) ≤ extendedRelativeEntropyNats A B := by
  unfold extendedRelativeEntropyNats
  refine le_iSup_of_le ({x} : Finset I) (le_of_eq ?_)
  have : Subsingleton (({x} : Finset I) : Type) := by
    constructor; rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.mem_singleton] at ha hb; subst ha hb; rfl
  have : Nonempty (({x} : Finset I) : Type) := ⟨⟨x, Finset.mem_singleton_self x⟩⟩
  rw [g66a_fre_one _ _ w hw]
  · rintro ⟨a, ha⟩; simp only [Finset.mem_singleton] at ha; subst ha; simpa using hA
  · rintro ⟨a, ha⟩; simp only [Finset.mem_singleton] at ha; subst ha; simpa using hB
def g66a_r (δ : ℝ) (K : ℕ) (k : ℕ) : ℝ := if k = 0 then 1 - δ else if k ≤ K then δ / K else 0

lemma g66a_r_nonneg (δ : ℝ) (K : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (k : ℕ) : 0 ≤ g66a_r δ K k := by
  unfold g66a_r; split_ifs <;> first | linarith | positivity

lemma g66a_r_supp (δ : ℝ) (K : ℕ) (k : ℕ) (hk : k ∉ Finset.range (K + 1)) : g66a_r δ K k = 0 := by
  simp only [Finset.mem_range, not_lt] at hk
  unfold g66a_r; rw [if_neg (by omega), if_neg (by omega)]

lemma g66a_sum_split (δ : ℝ) (K : ℕ) (hK : 0 < K) (h : ℕ → ℝ) (hh : ∀ k, k ≠ 0 → h k = g66a_r δ K k) :
    ∑ k ∈ Finset.range (K + 1), h k = h 0 + δ := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => δ / K)]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · intro k hk
    simp only [Finset.mem_range] at hk
    rw [hh _ (by omega)]; unfold g66a_r; rw [if_neg (by omega), if_pos (by omega)]

lemma g66a_r_sum (δ : ℝ) (K : ℕ) (hK : 0 < K) : ∑ k ∈ Finset.range (K + 1), g66a_r δ K k = 1 := by
  rw [g66a_sum_split δ K hK _ (fun k _ => rfl)]; simp [g66a_r]

lemma g66a_ofReal_tsum (b : ℕ → ℝ) (K : ℕ) (hb : ∀ k, 0 ≤ b k)
    (hs : ∀ k, k ∉ Finset.range (K + 1) → b k = 0) :
    (∑' k, ENNReal.ofReal (b k)) = ENNReal.ofReal (∑ k ∈ Finset.range (K + 1), b k) := by
  rw [tsum_eq_sum (s := Finset.range (K + 1)), ENNReal.ofReal_sum_of_nonneg (fun k _ => hb k)]
  intro k hk; rw [hs k hk, ENNReal.ofReal_zero]

def g66a_mu {I : Type} (f : ℕ → I) (δ : ℝ) (K : ℕ) (hK : 0 < K) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    CountableStateEnsemble I where
  weight k := ENNReal.ofReal (g66a_r δ K k)
  weight_sum := by
    rw [g66a_ofReal_tsum _ K (g66a_r_nonneg δ K h0 h1) (g66a_r_supp δ K), g66a_r_sum δ K hK]; simp
  state k := g66a_pure (f k)

def g66a_mu0 {I : Type} (x : I) : CountableStateEnsemble I where
  weight k := if k = 0 then 1 else 0
  weight_sum := tsum_ite_eq 0 1
  state _ := g66a_pure x

lemma g66a_holevo0 {I : Type} (x : I) : countableHolevo (g66a_mu0 x) = 0 := by
  unfold countableHolevo
  have hav : countableAverage (g66a_mu0 x) = g66a_P x := by
    ext i j
    simp only [countableAverage, g66a_mu0, g66a_pure]
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [hn]
  rw [hav]
  have : ∀ n, ((g66a_mu0 x).state n).coefficients = g66a_P x := fun _ => rfl
  simp only [this, g66a_relent_self, mul_zero, tsum_zero]
lemma g66a_avg {I : Type} (f : ℕ → I) (hf : Function.Injective f) (δ : ℝ) (K : ℕ) (hK : 0 < K)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (k : ℕ) :
    countableAverage (g66a_mu f δ K hK h0 h1) (f k) (f k) = (g66a_r δ K k : ℂ) := by
  simp only [countableAverage, g66a_mu, g66a_pure]
  rw [tsum_eq_single k]
  · simp [g66a_P_apply, ENNReal.toReal_ofReal (g66a_r_nonneg δ K h0 h1 k)]
  · intro n hn
    have : f k ≠ f n := fun h => hn (hf h).symm
    simp [g66a_P_apply, this]

lemma g66a_holevo_ge {I : Type} (f : ℕ → I) (hf : Function.Injective f) (δ : ℝ) (K : ℕ) (hK : 0 < K)
    (hδ : 0 < δ) (h1 : δ ≤ 1) :
    ENNReal.ofReal (δ * (-Real.log (δ / K) + δ / K - 1)) ≤
      countableHolevo (g66a_mu f δ K hK hδ.le h1) := by
  set X := -Real.log (δ / K) + δ / K - 1
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hc : 0 < δ / K := div_pos hδ hKr
  calc ENNReal.ofReal (δ * X) = ∑ k ∈ Finset.Icc 1 K, ENNReal.ofReal (δ / K) * ENNReal.ofReal X := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show K + 1 - 1 = K by omega,
          ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (g66a_mu f δ K hK hδ.le h1).weight k *
          extendedRelativeEntropyNats ((g66a_mu f δ K hK hδ.le h1).state k).coefficients
            (countableAverage (g66a_mu f δ K hK hδ.le h1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hr : g66a_r δ K k = δ / K := by unfold g66a_r; rw [if_neg (by omega), if_pos hk.2]
        have hw : (g66a_mu f δ K hK hδ.le h1).weight k = ENNReal.ofReal (δ / K) := by
          simp only [g66a_mu, hr]
        rw [hw]
        gcongr
        apply g66a_relent_single (f k) _ _ (δ / K) hc
        · simp [g66a_mu, g66a_pure, g66a_P_apply]
        · rw [g66a_avg f hf δ K hK hδ.le h1 k, hr]
    _ ≤ countableHolevo (g66a_mu f δ K hK hδ.le h1) := ENNReal.sum_le_tsum _
lemma g66a_smul_apply {I : Type} (c : ℂ) (u : Hilbert I) (i : I) : (c • u) i = c * u i := rfl

lemma g66a_ts_smul {I : Type} (c : ℝ) (x : I) (X : Matrix I I ℂ)
    (hX : ∀ i j, X i j = (c : ℂ) * g66a_P x i j) : traceSize X ≤ ENNReal.ofReal |c| := by
  refine (g66a_ts2 X ((c : ℂ) • g66a_e x) (g66a_e x) 0 0 ?_).trans (le_of_eq ?_)
  · intro i j; rw [hX]; simp only [g66a_P, g66a_smul_apply, lp.coeFn_zero, Pi.zero_apply, star_zero, mul_zero, add_zero]; ring
  · rw [norm_smul, g66a_e_norm]; simp

lemma g66a_d0 {I : Type} (f : ℕ → I) (δ : ℝ) (K : ℕ) (hK : 0 < K)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    distance0 (g66a_mu f δ K hK h0 h1) (g66a_mu0 (f 0)) ≤ ENNReal.ofReal (2 * δ) := by
  unfold distance0
  refine (ENNReal.half_le_self).trans ?_
  set b : ℕ → ℝ := fun k => if k = 0 then δ else g66a_r δ K k
  have hb : ∀ k, 0 ≤ b k := by intro k; simp only [b]; split_ifs; exact h0; exact g66a_r_nonneg δ K h0 h1 k
  calc _ ≤ ∑' k, ENNReal.ofReal (b k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k = 0
        · subst hk
          refine (g66a_ts_smul (-δ) (f 0) _ ?_).trans (le_of_eq ?_)
          · intro i j
            simp [g66a_mu, g66a_mu0, g66a_pure, g66a_r, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - δ)]
            ring
          · simp [b, abs_of_nonneg h0]
        · refine (g66a_ts_smul (g66a_r δ K k) (f k) _ ?_).trans (le_of_eq ?_)
          · intro i j
            simp [hk, g66a_mu, g66a_mu0, g66a_pure, ENNReal.toReal_ofReal (g66a_r_nonneg δ K h0 h1 k)]
          · simp [b, hk, abs_of_nonneg (g66a_r_nonneg δ K h0 h1 k)]
    _ = ENNReal.ofReal (2 * δ) := by
        rw [g66a_ofReal_tsum b K hb]
        · rw [g66a_sum_split δ K hK b (fun k hk => by simp [b, hk])]
          simp only [b, if_pos (rfl : (0:ℕ) = 0)]; ring_nf
        · intro k hk
          have : k ≠ 0 := by simp only [Finset.mem_range] at hk; omega
          simp only [b, if_neg this]; exact g66a_r_supp δ K k hk

lemma g66a_dK {I : Type} (f : ℕ → I) (δ : ℝ) (K : ℕ) (hK : 0 < K)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    distanceK (g66a_mu f δ K hK h0 h1) (g66a_mu0 (f 0)) ≤ ENNReal.ofReal (2 * δ) := by
  unfold distanceK
  set mu := g66a_mu f δ K hK h0 h1
  let P : ℕ → ℕ → ℝ≥0∞ := fun i j => if j = 0 then mu.weight i else 0
  have hfeas : EHSFeasible mu (g66a_mu0 (f 0)) P P := by
    constructor
    · intro i; simp [P]
    · intro j
      by_cases hj : j = 0
      · subst hj; simp [P, g66a_mu0, mu.weight_sum]
      · simp [P, hj, g66a_mu0]
  refine (iInf_le _ ⟨P, hfeas⟩).trans ?_
  set c : ℕ → ℝ := fun k => if k = 0 then 0 else g66a_r δ K k
  have hc : ∀ k, 0 ≤ c k := by intro k; simp only [c]; split_ifs; exact le_rfl; exact g66a_r_nonneg δ K h0 h1 k
  calc _ ≤ ∑' k, ENNReal.ofReal (c k) := by
        apply ENNReal.tsum_le_tsum
        intro i
        simp only [P]
        rw [tsum_eq_single 0 (fun j hj => by simp [hj])]
        simp only [if_true]
        by_cases hi : i = 0
        · subst hi
          have : extendedHalfTraceDistance (mu.state 0).coefficients ((g66a_mu0 (f 0)).state 0).coefficients = 0 := by
            unfold extendedHalfTraceDistance
            have := g66a_ts_smul 0 (f 0) ((mu.state 0).coefficients - ((g66a_mu0 (f 0)).state 0).coefficients)
              (fun i j => by simp [mu, g66a_mu, g66a_mu0, g66a_pure])
            simp at this
            simp [this]
          simp [this, c]
        · have hle : extendedHalfTraceDistance (mu.state i).coefficients ((g66a_mu0 (f 0)).state 0).coefficients ≤ 1 := by
            unfold extendedHalfTraceDistance
            have := g66a_ts2 ((mu.state i).coefficients - ((g66a_mu0 (f 0)).state 0).coefficients)
              (g66a_e (f i)) (g66a_e (f i)) (-g66a_e (f 0)) (g66a_e (f 0))
              (fun a b => by simp [mu, g66a_mu, g66a_mu0, g66a_pure, g66a_P]; ring)
            rw [norm_neg, g66a_e_norm, g66a_e_norm] at this
            norm_num at this
            rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
            simpa using this
          calc mu.weight i * _ ≤ mu.weight i * 1 := by gcongr
            _ = ENNReal.ofReal (c i) := by simp [mu, g66a_mu, c, hi]
    _ = ENNReal.ofReal δ := by
        rw [g66a_ofReal_tsum c K hc]
        · rw [g66a_sum_split δ K hK c (fun k hk => by simp [c, hk])]
          simp [c]
        · intro k hk
          have : k ≠ 0 := by simp only [Finset.mem_range] at hk; omega
          simp only [c, if_neg this]; exact g66a_r_supp δ K k hk
    _ ≤ ENNReal.ofReal (2 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
lemma g66a_bound (n : ℕ) :
    (1 : ℝ) ≤ (1 / ((n : ℝ) + 1)) * (-Real.log ((1 / ((n : ℝ) + 1)) / (⌈Real.exp (n + 2)⌉₊ : ℕ)) +
      (1 / ((n : ℝ) + 1)) / (⌈Real.exp (n + 2)⌉₊ : ℕ) - 1) := by
  set δ : ℝ := 1 / ((n : ℝ) + 1)
  set K : ℕ := ⌈Real.exp (n + 2)⌉₊
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    simp only [δ]; rw [div_le_one hn]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hKe : Real.exp (n + 2) ≤ (K : ℝ) := Nat.le_ceil _
  have hK : (0 : ℝ) < K := lt_of_lt_of_le (Real.exp_pos _) hKe
  have hlogK : (n : ℝ) + 2 ≤ Real.log K := (Real.le_log_iff_exp_le hK).mpr hKe
  have hlogd : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hl : Real.log (δ / K) = Real.log δ - Real.log K := Real.log_div hδ.ne' hK.ne'
  rw [hl]
  have hdK : 0 ≤ δ / K := by positivity
  have hmul : δ * ((n : ℝ) + 1) = 1 := by simp only [δ]; field_simp
  nlinarith

theorem g66a_main {I : Type} [Countable I] [Infinite I] :
    ∀ D : CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞,
      (D = distance0 ∨ D = distanceStar ∨ D = distanceK) →
      ¬ (∀ (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I),
        Tendsto (fun n => D (mu n) mu0) atTop (nhds 0) →
        Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0))) := by
  intro D hD hcont
  let f : ℕ → I := Infinite.natEmbedding I
  have hf : Function.Injective f := (Infinite.natEmbedding I).injective
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let K : ℕ → ℕ := fun n => ⌈Real.exp (n + 2)⌉₊
  have hK : ∀ n, 0 < K n := fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hδ1 : ∀ n, δ n ≤ 1 := fun n => by
    simp only [δ]; rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  let mu : ℕ → CountableStateEnsemble I := fun n => g66a_mu f (δ n) (K n) (hK n) (hδ n).le (hδ1 n)
  let mu0 := g66a_mu0 (f 0)
  have hDle : ∀ n, D (mu n) mu0 ≤ ENNReal.ofReal (2 * δ n) := by
    intro n
    rcases hD with rfl | rfl | rfl
    · exact g66a_d0 f (δ n) (K n) (hK n) (hδ n).le (hδ1 n)
    · show distanceStar (mu n) mu0 ≤ _
      unfold distanceStar
      exact (iInf_le_of_le (⟨mu n, rfl⟩ : {a // ensembleLaw a = ensembleLaw (mu n)})
        (iInf_le_of_le (⟨mu0, rfl⟩ : {b // ensembleLaw b = ensembleLaw mu0}) le_rfl)).trans
        (g66a_d0 f (δ n) (K n) (hK n) (hδ n).le (hδ1 n))
    · exact g66a_dK f (δ n) (K n) (hK n) (hδ n).le (hδ1 n)
  have hlim : Tendsto (fun n => ENNReal.ofReal (2 * δ n)) atTop (nhds 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
    rw [mul_zero] at this
    have h2 := ENNReal.tendsto_ofReal this
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have htend : Tendsto (fun n => D (mu n) mu0) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le) hDle
  have h := hcont mu mu0 htend
  rw [g66a_holevo0] at h
  have hev := h.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))
  obtain ⟨n, hn⟩ := hev.exists
  have hge := g66a_holevo_ge f hf (δ n) (K n) (hK n) (hδ n) (hδ1 n)
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (δ n * (-Real.log (δ n / (K n : ℕ)) + δ n / (K n : ℕ) - 1)) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (g66a_bound n)
  exact absurd (lt_of_le_of_lt (h1.trans hge) hn) (lt_irrefl _)

/-- PDF pp.25–26: chi fails continuity on ALL countable ensembles in infinite
dimension, for each distance. Sequential continuity is equivalent here. -/
theorem solution {I : Type} [Countable I] [Infinite I] :
    ∀ D : CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞,
      (D = distance0 ∨ D = distanceStar ∨ D = distanceK) →
      ¬ (∀ (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I),
        Tendsto (fun n => D (mu n) mu0) atTop (nhds 0) →
        Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0))) := g66a_main


end
