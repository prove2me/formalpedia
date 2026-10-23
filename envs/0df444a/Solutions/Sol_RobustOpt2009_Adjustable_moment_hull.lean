-- Prove2me | solution 1 for RobustOpt2009.Adjustable.moment_hull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:03:59.068166+00:00
-- url     : https://prove2.me/submissions/cc239e51-0244-4de6-909d-d76508599956

import Mathlib
import Definitions.Def_RobustOpt2009_Adjustable_Model
noncomputable section

open Matrix

namespace X8MH

variable {ι : Type*} [Fintype ι]

/-- quadratic form of a real matrix -/
def qf (G : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (G *ᵥ x)

def outer (x : ι → ℝ) : Matrix ι ι ℝ := vecMulVec x x

lemma qf_rot (G : Matrix ι ι ℝ) (a b : ι → ℝ) (c s : ℝ) :
    qf G (c • a + s • b) + qf G ((-s) • a + c • b) = (c ^ 2 + s ^ 2) * (qf G a + qf G b) := by
  simp only [qf, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma outer_rot (a b : ι → ℝ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    outer (c • a + s • b) + outer ((-s) • a + c • b) = outer a + outer b := by
  ext i j
  simp only [outer, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (a i * a j + b i * b j) * h

lemma qf_cont (G : Matrix ι ι ℝ) (a b : ι → ℝ) :
    Continuous fun t : ℝ => qf G (Real.cos t • a + Real.sin t • b) := by
  have : ∀ t : ℝ, qf G (Real.cos t • a + Real.sin t • b) =
      Real.cos t ^ 2 * qf G a + Real.cos t * Real.sin t * (a ⬝ᵥ (G *ᵥ b) + b ⬝ᵥ (G *ᵥ a)) +
        Real.sin t ^ 2 * qf G b := by
    intro t
    simp only [qf, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  simp_rw [this]
  fun_prop

lemma rot_exists (G : Matrix ι ι ℝ) (a b : ι → ℝ) (ha : 0 < qf G a) (hb : qf G b < 0) :
    ∃ y y' : ι → ℝ, outer y + outer y' = outer a + outer b ∧ qf G y = 0 ∧
      qf G y + qf G y' = qf G a + qf G b := by
  have hc := qf_cont G a b
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hivt := intermediate_value_Icc' hpi hc.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc (qf G (Real.cos (Real.pi / 2) • a + Real.sin (Real.pi / 2) • b))
      (qf G (Real.cos 0 • a + Real.sin 0 • b)) := by
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, zero_smul,
      one_smul, zero_add, add_zero]
    exact ⟨hb.le, ha.le⟩
  obtain ⟨t, -, ht⟩ := hivt h0
  have hcs : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq t
  refine ⟨Real.cos t • a + Real.sin t • b, (-Real.sin t) • a + Real.cos t • b,
    outer_rot a b _ _ hcs, ht, ?_⟩
  rw [qf_rot, hcs, one_mul]

/-- one-constraint rank-one decomposition (Sturm–Zhang) -/
lemma decomp (G : Matrix ι ι ℝ) : ∀ (n : ℕ) (s : Multiset (ι → ℝ)), s.card = n →
    (s.map (qf G)).sum ≤ 0 →
    ∃ s' : Multiset (ι → ℝ), (s'.map outer).sum = (s.map outer).sum ∧ ∀ y ∈ s', qf G y ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn hs
  by_cases hall : ∀ y ∈ s, qf G y ≤ 0
  · exact ⟨s, rfl, hall⟩
  push Not at hall
  obtain ⟨a, has, ha⟩ := hall
  obtain ⟨t1, rfl⟩ := Multiset.exists_cons_of_mem has
  have hs1 : (t1.map (qf G)).sum < 0 := by
    rw [Multiset.map_cons, Multiset.sum_cons] at hs; linarith
  obtain ⟨b, hbt, hb⟩ : ∃ b ∈ t1, qf G b < 0 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (t1.map (qf G)).sum := Multiset.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx; exact hc y hy)
    linarith
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hbt
  obtain ⟨y, y', hout, hy0, hsum⟩ := rot_exists G a b ha hb
  have hcard : (y' ::ₘ t).card < n := by
    rw [← hn]; simp
  have hs2 : ((y' ::ₘ t).map (qf G)).sum ≤ 0 := by
    simp only [Multiset.map_cons, Multiset.sum_cons] at hs ⊢; linarith
  obtain ⟨s', hs'1, hs'2⟩ := ih _ hcard (y' ::ₘ t) rfl hs2
  refine ⟨y ::ₘ s', ?_, ?_⟩
  · simp only [Multiset.map_cons, Multiset.sum_cons] at hs'1 ⊢
    rw [hs'1, ← add_assoc, hout, add_assoc]
  · intro z hz
    rcases Multiset.mem_cons.1 hz with rfl | hz
    · exact hy0.le
    · exact hs'2 z hz

end X8MH

open Matrix X8MH

namespace RobustOpt2009.Adjustable

variable {L r : ℕ}

def x8E (L : ℕ) : Matrix (Option (Fin L)) (Option (Fin L)) ℝ := momentBlock 1 0 0

def x8G (Q : Matrix (Fin r) (Fin L) ℝ) : Matrix (Option (Fin L)) (Option (Fin L)) ℝ :=
  momentBlock (-1) 0 (Qᵀ * Q)

def x8w (x : Option (Fin L) → ℝ) : Fin L → ℝ := fun j => x (some j)

lemma x8_lift_E (z : Fin L → ℝ) :
    quadraticLift z + x8E L = momentBlock 1 z (fun i j => z i * z j) := by
  ext i j
  cases i <;> cases j <;> simp [quadraticLift, momentBlock, x8E]

lemma x8_sumsq (Q : Matrix (Fin r) (Fin L) ℝ) (w : Fin L → ℝ) :
    ∑ i, (Q *ᵥ w) i ^ 2 = w ⬝ᵥ ((Qᵀ * Q) *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, sq]

lemma x8_qf_G (Q : Matrix (Fin r) (Fin L) ℝ) (x : Option (Fin L) → ℝ) :
    qf (x8G Q) x = ∑ i, (Q *ᵥ x8w x) i ^ 2 - x none ^ 2 := by
  rw [x8_sumsq]
  simp only [qf, dotProduct, Matrix.mulVec, Fintype.sum_option, x8G, momentBlock, x8w]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  ring

lemma x8_tr_outer {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) :
    trace (G * outer x) = qf G x := by
  simp only [trace, diag_apply, mul_apply, outer, vecMulVec_apply, qf, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma x8_tr_block (Q : Matrix (Fin r) (Fin L) ℝ) (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ) :
    trace (x8G Q * momentBlock 1 v W) = trace (Q * W * Qᵀ) - 1 := by
  have h1 : trace (x8G Q * momentBlock 1 v W) = trace ((Qᵀ * Q) * W) - 1 := by
    simp only [trace, diag_apply, mul_apply, Fintype.sum_option, x8G, momentBlock]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    ring
  rw [h1, Matrix.mul_assoc, Matrix.trace_mul_comm]

end RobustOpt2009.Adjustable

open Matrix X8MH

namespace RobustOpt2009.Adjustable

variable {L r : ℕ}

lemma x8_block_E (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ) :
    momentBlock 0 v W + x8E L = momentBlock 1 v W := by
  ext i j
  cases i <;> cases j <;> simp [momentBlock, x8E]

/-- the extended vector (1, z) -/
def x8ext (z : Fin L → ℝ) : Option (Fin L) → ℝ := fun o => Option.elim o 1 z

lemma x8_outer_ext (z : Fin L → ℝ) :
    outer (x8ext z) = momentBlock 1 z (fun i j => z i * z j) := by
  ext i j
  cases i <;> cases j <;> simp [outer, x8ext, momentBlock, vecMulVec_apply]

lemma x8_zero_mem (Q : Matrix (Fin r) (Fin L) ℝ) : (0 : Fin L → ℝ) ∈ ellipsoid Q := by
  simp [ellipsoid]

lemma x8_region_convex (Q : Matrix (Fin r) (Fin L) ℝ) : Convex ℝ (momentRegion Q) := by
  rintro M ⟨v1, W1, rfl, hP1, ht1⟩ M' ⟨v2, W2, rfl, hP2, ht2⟩ a b ha hb hab
  refine ⟨a • v1 + b • v2, a • W1 + b • W2, ?_, ?_, ?_⟩
  · ext i j
    cases i <;> cases j <;> simp [momentBlock]
  · have : momentBlock 1 (a • v1 + b • v2) (a • W1 + b • W2) =
        a • momentBlock 1 v1 W1 + b • momentBlock 1 v2 W2 := by
      ext i j
      cases i <;> cases j <;> simp [momentBlock, hab]
    rw [this]
    exact (hP1.smul ha).add (hP2.smul hb)
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    nlinarith

lemma x8_lift_region (Q : Matrix (Fin r) (Fin L) ℝ) (z : Fin L → ℝ) (hz : z ∈ ellipsoid Q) :
    quadraticLift z ∈ momentRegion Q := by
  refine ⟨z, fun i j => z i * z j, rfl, ?_, ?_⟩
  · rw [← x8_outer_ext]
    have := Matrix.posSemidef_vecMulVec_self_star (x8ext z)
    simpa [outer, star_trivial] using this
  · have h1 := x8_tr_block Q z (fun i j => z i * z j)
    rw [← x8_outer_ext, x8_tr_outer, x8_qf_G] at h1
    have h2 : x8w (x8ext z) = z := rfl
    rw [h2] at h1
    have h3 : x8ext z none = 1 := rfl
    rw [h3] at h1
    have := hz
    simp only [ellipsoid, Set.mem_ofPred_eq] at this
    linarith

lemma x8_hull_sub (Q : Matrix (Fin r) (Fin L) ℝ) : liftedHull Q ⊆ momentRegion Q := by
  refine convexHull_min ?_ (x8_region_convex Q)
  rintro _ ⟨z, hz, rfl⟩
  exact x8_lift_region Q z hz

lemma x8_corner (Q : Matrix (Fin r) (Fin L) ℝ) (p) (hp : p ∈ liftedHull Q) : p none none = 0 := by
  obtain ⟨v, W, rfl, -, -⟩ := x8_hull_sub Q hp
  rfl

lemma x8_outer_cone (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec)
    (y : Option (Fin L) → ℝ) (hy : qf (x8G Q) y ≤ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ p ∈ liftedHull Q, outer y = c • (p + x8E L) := by
  rw [x8_qf_G] at hy
  by_cases h0 : y none = 0
  · have hs : ∑ i, (Q *ᵥ x8w y) i ^ 2 = 0 := by
      rw [h0] at hy
      exact le_antisymm (by linarith) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have hz : Q *ᵥ x8w y = Q *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((Q *ᵥ x8w y) i))).1 hs i
        (Finset.mem_univ _)
      simpa using this
    have hw := hQ hz
    have hy0 : y = 0 := by
      funext o
      cases o with
      | none => exact h0
      | some j => exact congrFun hw j
    refine ⟨0, le_refl _, quadraticLift 0, subset_convexHull ℝ _ ⟨0, x8_zero_mem Q, rfl⟩, ?_⟩
    rw [hy0, zero_smul]
    ext i j; simp [outer]
  · set a := y none
    set z : Fin L → ℝ := fun j => y (some j) / a
    have hzw : z = a⁻¹ • x8w y := by funext j; simp [z, x8w, div_eq_inv_mul]
    have hz : z ∈ ellipsoid Q := by
      simp only [ellipsoid, Set.mem_ofPred_eq, hzw, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        mul_pow, ← Finset.mul_sum]
      rw [inv_pow]
      have ha2 : 0 < a ^ 2 := by positivity
      rw [inv_mul_le_iff₀ ha2]; linarith
    refine ⟨a ^ 2, sq_nonneg _, quadraticLift z, subset_convexHull ℝ _ ⟨z, hz, rfl⟩, ?_⟩
    have h0' : y none ≠ 0 := h0
    rw [x8_lift_E]
    ext i j
    cases i <;> cases j <;> simp [outer, momentBlock, vecMulVec_apply, z, a] <;> field_simp

lemma x8_cone (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec)
    (s : Multiset (Option (Fin L) → ℝ)) (hs : ∀ y ∈ s, qf (x8G Q) y ≤ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ p ∈ liftedHull Q, (s.map outer).sum = c • (p + x8E L) := by
  induction s using Multiset.induction_on with
  | empty =>
    exact ⟨0, le_refl _, quadraticLift 0, subset_convexHull ℝ _ ⟨0, x8_zero_mem Q, rfl⟩,
      by simp⟩
  | cons a s ih =>
    obtain ⟨c, hc, p, hp, hsum⟩ := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    obtain ⟨ca, hca, pa, hpa, ha⟩ := x8_outer_cone Q hQ a (hs a (Multiset.mem_cons_self a s))
    rw [Multiset.map_cons, Multiset.sum_cons, hsum, ha]
    by_cases hC : ca + c = 0
    · have h1 : ca = 0 := by linarith
      have h2 : c = 0 := by linarith
      exact ⟨0, le_refl _, p, hp, by rw [h1, h2]; simp⟩
    · have hCpos : 0 < ca + c := lt_of_le_of_ne (by linarith) (Ne.symm hC)
      refine ⟨ca + c, hCpos.le, (ca / (ca + c)) • pa + (c / (ca + c)) • p,
        convex_convexHull ℝ _ hpa hp (div_nonneg hca hCpos.le) (div_nonneg hc hCpos.le)
          (by field_simp), ?_⟩
      have e1 : (ca + c) * (ca / (ca + c)) = ca := mul_div_cancel₀ _ hC
      have e2 : (ca + c) * (c / (ca + c)) = c := mul_div_cancel₀ _ hC
      simp only [smul_add, smul_smul, e1, e2, add_smul]
      abel

lemma x8_region_sub (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec) :
    momentRegion Q ⊆ liftedHull Q := by
  rintro M ⟨v, W, rfl, hP, ht⟩
  obtain ⟨m, u, hX⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hP
  have hst : ∀ i, star (u i) = u i := fun i => funext fun j => star_trivial _
  simp only [hst] at hX
  set s : Multiset (Option (Fin L) → ℝ) := Finset.univ.val.map u with hsdef
  have hsout : (s.map outer).sum = momentBlock 1 v W := by
    rw [hX, hsdef, Multiset.map_map]; rfl
  have hsq : (s.map (qf (x8G Q))).sum ≤ 0 := by
    have : (s.map (qf (x8G Q))).sum = trace (x8G Q * momentBlock 1 v W) := by
      rw [hX, Matrix.mul_sum, Matrix.trace_sum, hsdef, Multiset.map_map]
      rw [Finset.sum_eq_multiset_sum]
      congr 1
      exact Multiset.map_congr rfl (fun i _ => (x8_tr_outer _ _).symm)
    rw [this, x8_tr_block]; linarith
  obtain ⟨s', hs'1, hs'2⟩ := decomp (x8G Q) _ s rfl hsq
  obtain ⟨c, -, p, hp, hcp⟩ := x8_cone Q hQ s' hs'2
  rw [hs'1, hsout] at hcp
  have hc1 : c = 1 := by
    have := congrFun (congrFun hcp none) none
    simp only [Matrix.smul_apply, Matrix.add_apply, x8_corner Q p hp, x8E, momentBlock,
      smul_eq_mul, zero_add, mul_one] at this
    exact this.symm
  rw [hc1, one_smul, ← x8_block_E] at hcp
  rw [add_right_cancel hcp]
  exact hp

theorem x8_eq (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec) :
    liftedHull Q = momentRegion Q :=
  Set.Subset.antisymm (x8_hull_sub Q) (x8_region_sub Q hQ)

end RobustOpt2009.Adjustable

open Matrix X8MH

namespace RobustOpt2009.Adjustable

variable {L r : ℕ}

lemma x8_ell_closed (Q : Matrix (Fin r) (Fin L) ℝ) : IsClosed (ellipsoid Q) := by
  have hc : Continuous fun z : Fin L → ℝ => ∑ i, (Q *ᵥ z) i ^ 2 := by
    have : Continuous fun z : Fin L → ℝ => Q *ᵥ z :=
      (Matrix.mulVecLin Q).continuous_of_finiteDimensional
    fun_prop
  exact isClosed_le hc continuous_const

lemma x8_ell_bdd (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec) :
    Bornology.IsBounded (ellipsoid Q) := by
  obtain ⟨K, -, hK⟩ := (Matrix.mulVecLin Q).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (by exact hQ))
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨K, fun z hz => ?_⟩
  rw [Metric.mem_closedBall]
  have h1 := hK.le_mul_dist z 0
  simp only [map_zero] at h1
  have h2 : dist ((Matrix.mulVecLin Q) z) 0 ≤ 1 := by
    rw [dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hz' : ∑ i, (Q *ᵥ z) i ^ 2 ≤ 1 := hz
    have : (Q *ᵥ z) i ^ 2 ≤ 1 := le_trans
      (Finset.single_le_sum (f := fun i => (Q *ᵥ z) i ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)) hz'
    have e : (Matrix.mulVecLin Q z) i = (Q *ᵥ z) i := rfl
    rw [Real.norm_eq_abs, e]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  calc dist z 0 ≤ K * dist ((Matrix.mulVecLin Q) z) 0 := h1
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2 K.2
    _ = K := mul_one _

lemma x8_lift_cont : Continuous (quadraticLift : (Fin L → ℝ) → _) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  cases i <;> cases j <;> simp only [quadraticLift, momentBlock] <;> fun_prop

lemma x8_psd_closed {ι : Type*} [Fintype ι] :
    IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have : {A : Matrix ι ι ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : ι → ℝ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_id) (isClosed_iInter fun x => ?_)
  refine isClosed_le continuous_const ?_
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

lemma x8_region_closed (Q : Matrix (Fin r) (Fin L) ℝ) : IsClosed (momentRegion Q) := by
  have : momentRegion Q = {M | M none none = 0} ∩ ({M | (M + x8E L).PosSemidef} ∩
      {M | trace (Q * M.submatrix some some * Qᵀ) ≤ 1}) := by
    ext M
    constructor
    · rintro ⟨v, W, rfl, hP, ht⟩
      refine ⟨rfl, ?_, ?_⟩
      · show (momentBlock 0 v W + x8E L).PosSemidef
        rw [x8_block_E]; exact hP
      · show trace (Q * (momentBlock 0 v W).submatrix some some * Qᵀ) ≤ 1
        have : (momentBlock 0 v W).submatrix some some = W := by ext i j; rfl
        rw [this]; exact ht
    · rintro ⟨h0, hP, ht⟩
      refine ⟨fun j => M none (some j), M.submatrix some some, ?_, ?_, ht⟩
      · have hH := hP.1
        ext i j
        cases i with
        | none => cases j with
          | none => exact h0
          | some j => rfl
        | some i => cases j with
          | none =>
            have := congrFun (congrFun hH none) (some i)
            simp [x8E, momentBlock, Matrix.conjTranspose_apply] at this
            simpa [momentBlock] using this
          | some j => rfl
      · have : momentBlock 1 (fun j => M none (some j)) (M.submatrix some some) = M + x8E L := by
          have hH := hP.1
          ext i j
          cases i with
          | none => cases j with
            | none => simp [momentBlock, x8E]; exact h0
            | some j => simp [momentBlock, x8E]
          | some i => cases j with
            | none =>
              have := congrFun (congrFun hH none) (some i)
              simp [x8E, momentBlock, Matrix.conjTranspose_apply] at this
              simpa [momentBlock, x8E] using this.symm
            | some j => simp [momentBlock, x8E]
        rw [this]; exact hP
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const) (IsClosed.inter ?_ ?_)
  · exact x8_psd_closed.preimage (continuous_id.add continuous_const)
  · refine isClosed_le ?_ continuous_const
    simp only [trace, diag_apply, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
    fun_prop

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem x8_main (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec) :
    Convex ℝ (liftedHull Q) ∧ IsCompact (liftedHull Q) ∧ liftedHull Q = momentRegion Q := by
  refine ⟨convex_convexHull ℝ _, ?_, x8_eq Q hQ⟩
  have hbdd : Bornology.IsBounded (liftedHull Q) := by
    unfold liftedHull
    rw [isBounded_convexHull]
    exact ((Metric.isCompact_of_isClosed_isBounded (x8_ell_closed Q) (x8_ell_bdd Q hQ)).image
      x8_lift_cont).isBounded
  have hcl : IsClosed (liftedHull Q) := by rw [x8_eq Q hQ]; exact x8_region_closed Q
  exact Metric.isCompact_of_isClosed_isBounded hcl hbdd

end RobustOpt2009.Adjustable

open RobustOpt2009.Adjustable in
theorem solution {L r : ℕ} (Q : Matrix (Fin r) (Fin L) ℝ)
    (hQ : Function.Injective Q.mulVec) :
    Convex ℝ (liftedHull Q) ∧ IsCompact (liftedHull Q) ∧
      liftedHull Q = momentRegion Q :=
  x8_main Q hQ
