-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P28.covariant_seed_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:17:00.315311+00:00
-- url     : https://prove2.me/submissions/ef9d3a00-ceb5-4a70-86a2-e52f2658f2ca

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)


instance g67h_borel (d : ℕ) : BorelSpace (SU d) := ⟨rfl⟩

instance g67h_compact (d : ℕ) : CompactSpace (SU d) := by
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ : Set ((Matrix (Fin d) (Fin d) ℂ))) :=
    isClosed_unitary.inter (isClosed_eq
      (show Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => A.det) from
        continuous_id.matrix_det) continuous_const)
  have hK : IsCompact (Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hc ?_)
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_norm_bound_of_unitary hU.1 i j

lemma g67h_inv {d : ℕ} {haar : Measure (SU d)} (h : IsProbabilityHaar haar) :
    haar.IsMulLeftInvariant := ⟨fun g => (h.2 g).map_eq⟩

theorem g67h_coe_cont {d : ℕ} (i j : Fin d) :
    Continuous (fun U : SU d => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g67h_F_cont {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Continuous (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_finsetSum _ fun l _ => (g67h_coe_cont i l).mul continuous_const).mul
      (g67h_coe_cont j k).star
theorem g67h_scalar {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T) :
    ∀ a b, T a b = if a = b then T a a else 0 := by
  intro a b
  split_ifs with hab
  · subst hab; rfl
  · -- diagonal sign matrix
    set s : Fin d → ℂ := fun k => if k = a then -1 else 1
    have hW : Matrix.diagonal s ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]; congr 1; funext k
      simp only [s, Pi.star_apply]; split_ifs <;> simp
    have := congrFun (congrFun (h _ hW) a) b
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simp only [Pi.star_apply, s, if_pos rfl, if_neg (Ne.symm hab), star_one, mul_one] at this
    have : 2 * T a b = 0 := by linear_combination -this
    simpa using this

theorem g67h_diag {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T) (a b : Fin d) :
    T a a = T b b := by
  set W : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => if j = Equiv.swap a b i then 1 else 0
  have hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    simp only [W, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, (Equiv.swap a b).injective.ne hij, eq_comm]
  have := congrFun (congrFun (h _ hW) a) a
  rw [← this]
  simp only [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp only [apply_ite star, star_one, star_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul]
  simp [Finset.sum_ite_eq', Equiv.swap_apply_left]

theorem g67h_root {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ c • W ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  set w := W.det
  have hw : star w * w = 1 := by
    have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    exact this
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  set r : ℂ := w ^ ((d : ℂ)⁻¹)
  have hr : r ^ d = w := Complex.cpow_nat_inv_pow w (by omega)
  have hr0 : r ≠ 0 := by intro h0; rw [h0, zero_pow (by omega)] at hr; exact hw0 hr.symm
  have hrn : ‖r‖ = 1 := by
    have h2 : ‖w‖ = 1 := by
      have : ‖star w * w‖ = 1 := by rw [hw]; simp
      rw [norm_mul, norm_star] at this
      nlinarith [norm_nonneg w]
    rw [← hr, norm_pow] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg r) (by omega)).mp h2
  refine ⟨r⁻¹, ?_, ?_⟩
  · have : star r * r = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hrn]; simp
    rw [star_inv₀, ← mul_inv, this, inv_one]
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hW ⊢
      rw [star_smul, smul_mul_smul_comm, hW]
      have : r⁻¹ * star r⁻¹ = 1 := by
        rw [star_inv₀, Complex.star_def, ← mul_inv, Complex.mul_conj', hrn]; simp
      rw [this, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hr]
      exact inv_mul_cancel₀ hw0

theorem g67h_twirl {d : ℕ} (hd : 0 < d) (mu : Measure (SU d)) [mu.IsMulLeftInvariant]
    [IsProbabilityMeasure mu] (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Integrable (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) mu ∧
    (∫ U : SU d, ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j ∂mu) =
      (X.trace / d) * (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  have hint : ∀ i j, Integrable (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) mu := fun i j =>
    (g67h_F_cont X i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint i j, ?_⟩
  set T : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => ∫ U : SU d,
    ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j ∂mu with hT
  -- invariance under SU
  have hSU : ∀ V : SU d, (V : Matrix (Fin d) (Fin d) ℂ) * T * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ = T := by
    intro V
    ext a b
    have e1 : ∀ U : SU d, ((V * U : SU d) : Matrix (Fin d) (Fin d) ℂ) * X * ((V * U : SU d) : Matrix (Fin d) (Fin d) ℂ)ᴴ
        = (V : Matrix (Fin d) (Fin d) ℂ) * ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
          (V : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
      intro U
      rw [Submonoid.coe_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    have e2 := integral_mul_left_eq_self (μ := mu) (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) a b) V
    simp only [e1] at e2
    rw [hT, Matrix.of_apply, ← e2]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_mul_const, integral_finsetSum]
      · refine congrArg (· * _) (Finset.sum_congr rfl fun l _ => ?_)
        rw [integral_const_mul]
      · intro l _; exact (hint l k).const_mul _
    · intro k _
      exact (integrable_finsetSum _ fun l _ => (hint l k).const_mul _).mul_const _
  have hU : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T := by
    intro W hW
    obtain ⟨c, hc, hcW⟩ := g67h_root hd W hW
    have := hSU ⟨c • W, hcW⟩
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at this
    rw [show star c * c = 1 from hc, one_smul] at this
    exact this
  -- trace
  have htr : T.trace = X.trace := by
    simp only [Matrix.trace, Matrix.diag, hT, Matrix.of_apply]
    rw [← integral_finsetSum _ fun k _ => hint k k]
    have : ∀ U : SU d, ∑ k, ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) k k = X.trace := by
      intro U
      have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp U.2.1
      have := Matrix.trace_mul_cycle (U : Matrix (Fin d) (Fin d) ℂ) X (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
      rw [h1, Matrix.one_mul] at this
      exact this
    simp only [this, integral_const, probReal_univ, one_smul]
    rfl
  have hsc := g67h_scalar T hU
  have hdg := g67h_diag T hU
  have a0 : Fin d := ⟨0, hd⟩
  have htr2 : T.trace = d * T i i := by
    simp only [Matrix.trace, Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => hdg k i]; simp
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hii : T i i = X.trace / d := by rw [← htr, htr2]; field_simp
  change T i j = _
  rw [hsc i j, Matrix.one_apply]
  split_ifs with h
  · rw [hii]; ring
  · ring

theorem g67h_ent {d : ℕ} (hd : 0 < d) (mu : Measure (SU d)) [mu.IsMulLeftInvariant]
    [IsProbabilityMeasure mu] (p a q c : Fin d) :
    Integrable (fun U : SU d => (U : Op (Fin d)) p a * star ((U : Op (Fin d)) q c)) mu ∧
    (∫ U : SU d, (U : Op (Fin d)) p a * star ((U : Op (Fin d)) q c) ∂mu) =
      (if a = c then (d : ℂ)⁻¹ else 0) * (if p = q then 1 else 0) := by
  have e : ∀ U : SU d, (U : Op (Fin d)) p a * star ((U : Op (Fin d)) q c) =
      ((U : Op (Fin d)) * (Matrix.single a c (1 : ℂ) : Op (Fin d)) * (U : Op (Fin d))ᴴ) p q := by
    intro U
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, mul_ite, mul_one,
      mul_zero, ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp only [e]
  obtain ⟨h1, h2⟩ := g67h_twirl hd mu (Matrix.single a c (1 : ℂ) : Op (Fin d)) p q
  refine ⟨h1, ?_⟩
  have ht : (Matrix.single a c (1 : ℂ) : Op (Fin d)).trace = if a = c then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.single_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => if_neg fun h => hb h.1.symm) (by simp)]
    by_cases h : a = c <;> simp [h, eq_comm]
  rw [h2, ht, Matrix.one_apply]
  split_ifs <;> simp [div_eq_mul_inv]

lemma g67h_mat_integrable {n : Type*} [Fintype n] {_i : DecidableEq n} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : α → Matrix n n ℂ) (h : ∀ i j, Integrable (fun x => F x i j) μ) :
    Integrable F μ := by
  have : F = fun x => ∑ i, ∑ j, F x i j • (Matrix.single i j (1 : ℂ) : Matrix n n ℂ) := by
    funext x
    conv_lhs => rw [Matrix.matrix_eq_sum_single (F x)]
    simp [Matrix.smul_single]
  rw [this]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (h i j).smul_const _

lemma g67h_mat_entry {n : Type*} [Fintype n] {_i : DecidableEq n} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : α → Matrix n n ℂ) (hF : Integrable F μ) (i j : n) :
    (∫ x, F x ∂μ) i j = ∫ x, F x i j ∂μ :=
  ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).integral_comp_comm hF).symm

lemma g67h_conj_entry {d : ℕ} (g : GroupPair d) (A : Op (ChoiBasis d)) (p q : ChoiBasis d) :
    conjugateTesterSeed g A p q = ∑ x, ∑ y, A x y *
      (((g.1 : Op (Fin d)) p.1 x.1 * star ((g.1 : Op (Fin d)) q.1 y.1)) *
       ((g.2 : Op (Fin d)) p.2 x.2 * star ((g.2 : Op (Fin d)) q.2 y.2))) := by
  simp only [conjugateTesterSeed, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul']
  ring

lemma g67h_pair {d : ℕ} (hd : 0 < d) (haar : Measure (SU d)) [haar.IsMulLeftInvariant]
    [IsProbabilityMeasure haar] (A : Op (ChoiBasis d)) (p q : ChoiBasis d) :
    Integrable (fun g : GroupPair d => conjugateTesterSeed g A p q) (haar.prod haar) ∧
    (∫ g : GroupPair d, conjugateTesterSeed g A p q ∂(haar.prod haar)) =
      A.trace / (d : ℂ)^2 * (if p = q then 1 else 0) := by
  simp only [g67h_conj_entry]
  have hI : ∀ x y : ChoiBasis d, Integrable (fun g : GroupPair d =>
      ((g.1 : Op (Fin d)) p.1 x.1 * star ((g.1 : Op (Fin d)) q.1 y.1)) *
       ((g.2 : Op (Fin d)) p.2 x.2 * star ((g.2 : Op (Fin d)) q.2 y.2))) (haar.prod haar) :=
    fun x y => (g67h_ent hd haar p.1 x.1 q.1 y.1).1.mul_prod (g67h_ent hd haar p.2 x.2 q.2 y.2).1
  refine ⟨integrable_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ => (hI x y).const_mul _, ?_⟩
  have h1 : (∫ g : GroupPair d, ∑ x, ∑ y, A x y *
      (((g.1 : Op (Fin d)) p.1 x.1 * star ((g.1 : Op (Fin d)) q.1 y.1)) *
       ((g.2 : Op (Fin d)) p.2 x.2 * star ((g.2 : Op (Fin d)) q.2 y.2))) ∂(haar.prod haar)) =
      ∑ x, ∑ y, A x y * (((if x.1 = y.1 then (d : ℂ)⁻¹ else 0) * (if p.1 = q.1 then 1 else 0)) *
        ((if x.2 = y.2 then (d : ℂ)⁻¹ else 0) * (if p.2 = q.2 then 1 else 0))) := by
    set F : ChoiBasis d → ChoiBasis d → GroupPair d → ℂ := fun x y g =>
      (((g.1 : Op (Fin d)) p.1 x.1 * star ((g.1 : Op (Fin d)) q.1 y.1)) *
       ((g.2 : Op (Fin d)) p.2 x.2 * star ((g.2 : Op (Fin d)) q.2 y.2))) with hF
    rw [integral_finset_sum (f := fun x g => ∑ y, A x y * F x y g) _
      fun x _ => integrable_finset_sum _ fun y _ => (hI x y).const_mul _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finset_sum (f := fun y g => A x y * F x y g) _ fun y _ => (hI x y).const_mul _]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [integral_prod_mul (fun U : SU d => (U : Op (Fin d)) p.1 x.1 * star ((U : Op (Fin d)) q.1 y.1))
      (fun U : SU d => (U : Op (Fin d)) p.2 x.2 * star ((U : Op (Fin d)) q.2 y.2)),
      (g67h_ent hd haar _ _ _ _).2, (g67h_ent hd haar _ _ _ _).2]
  rw [h1]
  simp only [Fintype.sum_prod_type]
  simp only [ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const_zero]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, Finset.sum_ite_eq, Finset.mem_univ]
    rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.diag]
    field_simp
  · rw [if_neg hpq]
    have : ¬ p.1 = q.1 ∨ ¬ p.2 = q.2 := by
      by_contra h; push_neg at h; exact hpq (Prod.ext h.1 h.2)
    rcases this with h | h <;> simp [h]

/-- PDF pp.2–3, (24)–(25): arbitrary positive seeds give a normalized covariant
tester exactly when their traces sum to d; zero seed effects need not be divided by. -/
theorem solution {d : ℕ} (hd : 0 < d)
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (hP : ∀ j, (P j).PosSemidef) :
    (∫ z, covariant P z ∂(Measure.count.prod (haar.prod haar))) =
      ((∑ j, (P j).trace) / (d : ℂ)^2) • (1 : Op (ChoiBasis d)) ∧
    (IsTesterDensity (Measure.count.prod (haar.prod haar)) (covariant P) ↔
      ∑ j, (P j).trace = (d : ℂ)) := by


  haveI := g67h_inv hhaar
  haveI := hhaar.1
  have hent : ∀ p q, Integrable (fun z => covariant P z p q) (Measure.count.prod (haar.prod haar)) ∧
      (∫ z, covariant P z p q ∂(Measure.count.prod (haar.prod haar))) =
        (∑ j, (P j).trace) / (d : ℂ)^2 * (if p = q then 1 else 0) := by
    intro p q
    have e : ∀ z : J × GroupPair d, covariant P z p q =
        ∑ j, (fun j' : J => if j' = j then (1 : ℂ) else 0) z.1 * conjugateTesterSeed z.2 (P j) p q := by
      intro z
      simp [covariant, Finset.sum_ite_eq']
    simp only [e]
    have hI : ∀ j, Integrable (fun z : J × GroupPair d =>
        (fun j' : J => if j' = j then (1 : ℂ) else 0) z.1 * conjugateTesterSeed z.2 (P j) p q)
        (Measure.count.prod (haar.prod haar)) := fun j =>
      (Integrable.of_finite (μ := Measure.count) (f := fun j' : J => if j' = j then (1 : ℂ) else 0)).mul_prod (g67h_pair hd haar (P j) p q).1
    refine ⟨integrable_finset_sum _ fun j _ => hI j, ?_⟩
    rw [integral_finset_sum _ fun j _ => hI j]
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun j' : J => if j' = j then (1 : ℂ) else 0)
      (fun g : GroupPair d => conjugateTesterSeed g (P j) p q), (g67h_pair hd haar _ p q).2]
    simp [integral_fintype]
  have hint : Integrable (covariant P) (Measure.count.prod (haar.prod haar)) :=
    g67h_mat_integrable _ fun p q => (hent p q).1
  have hI : (∫ z, covariant P z ∂(Measure.count.prod (haar.prod haar))) =
      ((∑ j, (P j).trace) / (d : ℂ)^2) • (1 : Op (ChoiBasis d)) := by
    refine Matrix.ext fun p q => ?_
    rw [g67h_mat_entry _ hint, (hent p q).2, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨hI, ?_, ?_⟩
  · rintro ⟨-, -, σ, hσ, h⟩
    have hM : Matrix.kronecker (1 : Op (Fin d)) σ =
        ((∑ j, (P j).trace) / (d : ℂ)^2) • (1 : Op (ChoiBasis d)) := by
      refine Matrix.ext fun p q => ?_
      rw [← h, g67h_mat_entry _ (g67h_mat_integrable _ fun p q => (hent p q).1), (hent p q).2,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have := congrArg Matrix.trace hM
    unfold Matrix.kronecker at this
    rw [Matrix.trace_kronecker, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_one, hσ.2] at this
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, smul_eq_mul, mul_one] at this
    field_simp at this
    linear_combination -this
  · intro hsum
    refine ⟨g67h_mat_integrable _ fun p q => (hent p q).1, fun z => ?_, (d : ℂ)⁻¹ • (1 : Op (Fin d)),
      ⟨?_, ?_⟩, ?_⟩
    · exact (hP z.1).mul_mul_conjTranspose_same _
    · refine Matrix.PosSemidef.one.smul ?_
      have : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this]; exact_mod_cast (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ hd0]
    · refine Matrix.ext fun p q => ?_
      rw [g67h_mat_entry _ (g67h_mat_integrable _ fun p q => (hent p q).1), (hent p q).2, hsum]
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Prod.ext_iff]
      by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2] <;> field_simp
