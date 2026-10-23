-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P13.example21_bell_nonunique_closest_states
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:51:15.251598+00:00
-- url     : https://prove2.me/submissions/4fcbb770-88b1-4d91-9326-b0ac360b5e8a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

-- ===== P13A =====


open Matrix ComplexConjugate
open scoped ComplexOrder

namespace X6P13

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- quadratic form `⟨v|M|v⟩` -/
def qf (M : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ := ∑ a, ∑ b, star (v a) * M a b * v b

lemma cfc_entry {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (a b : ι) :
    cfc f A a b = ∑ i, (hA.eigenvectorBasis i) a * (f (hA.eigenvalues i) : ℂ) *
      star ((hA.eigenvectorBasis i) b) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  rfl

/-- coefficient of `v` along the `i`-th eigenvector -/
def co {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) (i : ι) : ℂ :=
  star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ v

lemma qf_cfc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (v : ι → ℂ) :
    qf (cfc f A) v = ∑ i, (f (hA.eigenvalues i) : ℂ) * ((‖co hA v i‖ ^ 2 : ℝ) : ℂ) := by
  have hco : ∀ i, ((‖co hA v i‖ ^ 2 : ℝ) : ℂ) =
      (∑ a, star (v a) * (hA.eigenvectorBasis i) a) *
        (∑ b, star ((hA.eigenvectorBasis i) b) * v b) := by
    intro i
    have h1 : (∑ a, star (v a) * (hA.eigenvectorBasis i) a) = star (co hA v i) := by
      simp only [co, dotProduct, star_sum, star_mul, star_star, Pi.star_apply]
    rw [h1]
    have h2 : (∑ b, star ((hA.eigenvectorBasis i) b) * v b) = co hA v i := by
      simp only [co, dotProduct, Pi.star_apply]
    rw [h2, RCLike.star_def, Complex.conj_mul']
    push_cast; ring
  simp_rw [hco]
  unfold qf
  simp_rw [cfc_entry hA]
  calc _ = ∑ a, ∑ b, ∑ i, star (v a) * ((hA.eigenvectorBasis i) a *
          (f (hA.eigenvalues i) : ℂ) * star ((hA.eigenvectorBasis i) b)) * v b := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ i, ∑ b, star (v a) * ((hA.eigenvectorBasis i) a *
          (f (hA.eigenvalues i) : ℂ) * star ((hA.eigenvectorBasis i) b)) * v b := by
        apply Finset.sum_congr rfl; intro a _
        exact Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, star (v a) * ((hA.eigenvectorBasis i) a *
          (f (hA.eigenvalues i) : ℂ) * star ((hA.eigenvectorBasis i) b)) * v b :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _
        ring

lemma qf_one_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    qf 1 v = ∑ i, ((‖co hA v i‖ ^ 2 : ℝ) : ℂ) := by
  have := qf_cfc hA (fun _ => 1) v
  rw [cfc_const_one ℝ A] at this
  simpa using this

lemma qf_self_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    qf A v = ∑ i, (hA.eigenvalues i : ℂ) * ((‖co hA v i‖ ^ 2 : ℝ) : ℂ) := by
  have := qf_cfc hA (fun x => x) v
  rw [cfc_id' ℝ A] at this
  exact this

lemma co_eig {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) (μ : ℝ)
    (hv : A *ᵥ v = (μ : ℂ) • v) (i : ι) : co hA v i = 0 ∨ hA.eigenvalues i = μ := by
  have key : (hA.eigenvalues i : ℂ) * co hA v i = (μ : ℂ) * co hA v i := by
    have h1 : star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * co hA v i := by
      rw [hv, dotProduct_smul, smul_eq_mul]; rfl
    have h2 : star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (A *ᵥ v) =
        (hA.eigenvalues i : ℂ) * co hA v i := by
      rw [dotProduct_mulVec]
      have : star (⇑(hA.eigenvectorBasis i)) ᵥ* A = star (A *ᵥ ⇑(hA.eigenvectorBasis i)) := by
        rw [star_mulVec, hA.eq]
      rw [this, hA.mulVec_eigenvectorBasis, star_smul]
      simp [co, smul_dotProduct]
    rw [← h1, ← h2]
  by_cases h : co hA v i = 0
  · exact Or.inl h
  · right
    have := mul_right_cancel₀ h key
    exact_mod_cast this

lemma qf_eig {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) (μ : ℝ)
    (hv : A *ᵥ v = (μ : ℂ) • v) (f : ℝ → ℝ) : qf (cfc f A) v = (f μ : ℂ) * qf 1 v := by
  rw [qf_cfc hA, qf_one_eq hA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases co_eig hA v μ hv i with h | h
  · simp [h]
  · rw [h]

/-- Jensen bound `⟨v|log A|v⟩ ≤ log ⟨v|A|v⟩` for unit `v` in the support of `A ≥ 0`. -/
lemma log_qf_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (v : ι → ℂ) (hv : qf 1 v = 1)
    (hker : ∀ i, hA.1.eigenvalues i = 0 → co hA.1 v i = 0) :
    (qf (cfc Real.log A) v).re ≤ Real.log (qf A v).re := by
  set w : ι → ℝ := fun i => ‖co hA.1 v i‖ ^ 2 with hw
  set lam := hA.1.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := hA.eigenvalues_nonneg
  have hsum : ∑ i, w i = 1 := by
    have := congrArg Complex.re (qf_one_eq hA.1 v)
    rw [hv] at this
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at this
    exact this.symm
  have e1 : (qf (cfc Real.log A) v).re = ∑ i, w i * Real.log (lam i) := by
    rw [qf_cfc hA.1, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]; ring
  have e2 : (qf A v).re = ∑ i, w i * lam i := by
    rw [qf_self_eq hA.1, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]; ring
  rw [e1, e2]
  set t := Finset.univ.filter fun i => w i ≠ 0
  have hpos : ∀ i ∈ t, 0 < lam i := by
    intro i hi
    have hwi : w i ≠ 0 := (Finset.mem_filter.1 hi).2
    rcases (hlam i).lt_or_eq with h | h
    · exact h
    · exfalso; apply hwi; simp [w, hker i h.symm]
  have hrest : ∀ g : ι → ℝ, ∑ i, w i * g i = ∑ i ∈ t, w i * g i := by
    intro g
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  rw [hrest, hrest]
  have hsum' : ∑ i ∈ t, w i = 1 := by
    rw [← hsum, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    split_ifs with h
    · rfl
    · push Not at h; exact h.symm
  have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := t) (w := w) (p := lam)
    (fun i _ => by positivity) hsum' (fun i hi => hpos i hi)
  simpa [smul_eq_mul] using this

end X6P13

-- ===== P13B =====


open Matrix ComplexConjugate
open scoped ComplexOrder

attribute [local instance] Classical.propDecidable

namespace X6P13

open QAlgorithms.Papers.Independent.Dependency50.P13

/-- the Bell vector -/
def phi : Bool × Bool → ℂ := fun p => if p.1 = p.2 then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

lemma c_sq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

lemma c2 : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

lemma bell_eq : bellState = Matrix.of fun a b => phi a * star (phi b) := by
  ext a b
  simp only [bellState, QAlgorithms.pureDensity, QAlgorithms.maxEntangled, phi, Matrix.of_apply]
  have h1 : ∀ p : Bool × Bool, ((fun _ : Fin 1 => p.1) = (fun _ => p.2)) ↔ p.1 = p.2 := by
    intro p
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext; exact h
  simp only [h1, pow_one]
  split_ifs <;> simp

lemma bell_apply (a b : Bool × Bool) :
    bellState a b = if a.1 = a.2 ∧ b.1 = b.2 then 1 / 2 else 0 := by
  rw [bell_eq]
  simp only [Matrix.of_apply, phi]
  split_ifs <;> simp_all [c2]

lemma qf_one_phi : qf 1 phi = 1 := by
  simp only [qf, Matrix.one_apply, phi]
  simp [Fintype.sum_prod_type, c2]
  norm_num

lemma bell_idem : bellState * bellState = bellState := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [bell_apply]
  rcases a with ⟨_ | _, _ | _⟩ <;> rcases b with ⟨_ | _, _ | _⟩ <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

lemma bell_herm : bellStateᴴ = bellState := by
  ext a b
  simp only [Matrix.conjTranspose_apply, bell_apply]
  split_ifs <;> simp_all

lemma bell_trace : bellState.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, bell_apply]
  simp [Fintype.sum_prod_type]

lemma trace_bell_mul (L : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (bellState * L).trace = qf L phi := by
  rw [bell_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, qf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-! ### two-level functional calculus (from X6P41) -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma two_selfAdjoint (P : Matrix ι ι ℂ) (hPh : Pᴴ = P) (a b : ℝ) :
    IsSelfAdjoint ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
  show ((a : ℂ) • P + (b : ℂ) • (1 - P))ᴴ = _
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_one, hPh]
  simp

lemma spectrum_two (P : Matrix ι ι ℂ) (hP : P * P = P) (a b : ℝ) (r : ℝ)
    (hr : r ∈ spectrum ℝ ((a : ℂ) • P + (b : ℂ) • (1 - P))) : r = a ∨ r = b := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  apply (spectrum.mem_iff.1 hr)
  have ha' : ((r : ℂ) - a) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast ha
  have hb' : ((r : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  set Y : Matrix ι ι ℂ := ((r : ℂ) - a)⁻¹ • P + ((r : ℂ) - b)⁻¹ • (1 - P)
  have hX : algebraMap ℝ (Matrix ι ι ℂ) r - ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      ((r : ℂ) - a) • P + ((r : ℂ) - b) • (1 - P) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (r • (1 : Matrix ι ι ℂ)) = (r : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    simp only [sub_smul, smul_sub]
    abel
  rw [hX]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hP1, sub_zero]
  refine isUnit_iff_exists.2 ⟨Y, ?_, ?_⟩
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, mul_inv_cancel₀ ha', mul_inv_cancel₀ hb', one_smul]
    abel
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, inv_mul_cancel₀ ha', inv_mul_cancel₀ hb', one_smul]
    abel

lemma cfc_zero_of_proj (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (f : ℝ → ℝ)
    (h0 : f 0 = 0) (h1 : f 1 = 0) : cfc f P = 0 := by
  have hPe : P = ((1 : ℝ) : ℂ) • P + ((0 : ℝ) : ℂ) • (1 - P) := by simp
  have hsa := two_selfAdjoint P hPh 1 0
  rw [← hPe] at hsa
  have : cfc f P = cfc (fun _ => (0 : ℝ)) P := by
    apply cfc_congr
    intro r hr
    rw [hPe] at hr
    rcases spectrum_two P hP 1 0 r hr with h | h <;> subst h <;> simp [h0, h1]
  rw [this, cfc_const_zero]

end

lemma cfc_xlogx_bell : cfc (fun x : ℝ => x * Real.log x) bellState = 0 :=
  cfc_zero_of_proj _ bell_idem bell_herm _ (by simp) (by simp)

/-- relative entropy from the Bell state to a trace-one state -/
lemma qRel_bell (σ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hσ : σ.trace = 1) :
    QAlgorithms.qRelEntropy bellState σ = -(qf (cfc Real.log σ) phi).re := by
  unfold QAlgorithms.qRelEntropy
  rw [cfc_xlogx_bell, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, hσ, bell_trace,
    trace_bell_mul]
  simp

/-! ### the two closest separable states -/

lemma sigma1_apply (a b : Bool × Bool) :
    bellSigmaOne a b = (1 / 2 : ℂ) * bellState a b + (1 / 6 : ℂ) *
      ((1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) a b - bellState a b) := by
  simp [bellSigmaOne]

lemma sigma2_apply (a b : Bool × Bool) :
    bellSigmaTwo a b = (1 / 2 : ℂ) * bellState a b + (1 / 4 : ℂ) *
      (qubitPairProjector (false, true) a b + qubitPairProjector (true, false) a b) := by
  simp [bellSigmaTwo]; ring

lemma sigma1_phi : bellSigmaOne *ᵥ phi = ((1 / 2 : ℝ) : ℂ) • phi := by
  funext a
  simp only [Matrix.mulVec, dotProduct, sigma1_apply, bell_apply, Matrix.one_apply, phi,
    Pi.smul_apply, smul_eq_mul]
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

lemma sigma2_phi : bellSigmaTwo *ᵥ phi = ((1 / 2 : ℝ) : ℂ) • phi := by
  funext a
  simp only [Matrix.mulVec, dotProduct, sigma2_apply, bell_apply, qubitPairProjector, phi,
    Pi.smul_apply, smul_eq_mul]
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

lemma bell_sigma1 : bellState * bellSigmaOne = (1 / 2 : ℂ) • bellState := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [sigma1_apply, bell_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  rcases a with ⟨_ | _, _ | _⟩ <;> rcases b with ⟨_ | _, _ | _⟩ <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

lemma bell_sigma2 : bellState * bellSigmaTwo = (1 / 2 : ℂ) • bellState := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [sigma2_apply, bell_apply, qubitPairProjector, Matrix.smul_apply, smul_eq_mul]
  rcases a with ⟨_ | _, _ | _⟩ <;> rcases b with ⟨_ | _, _ | _⟩ <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

lemma ker_of_mul (σ : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (h : bellState * σ = (1 / 2 : ℂ) • bellState) :
    LinearMap.ker σ.mulVecLin ≤ LinearMap.ker bellState.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have : bellState *ᵥ v = (2 : ℂ) • ((bellState * σ) *ᵥ v) := by
    rw [h, Matrix.smul_mulVec, smul_smul]; norm_num
  rw [this, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero]

lemma rel_of_eig (σ : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hh : σ.IsHermitian)
    (hσ : σ.trace = 1) (hv : σ *ᵥ phi = ((1 / 2 : ℝ) : ℂ) • phi)
    (h : bellState * σ = (1 / 2 : ℂ) • bellState) :
    twoQubitRelativeEntropy bellState σ = ENNReal.ofReal (Real.log 2) := by
  unfold twoQubitRelativeEntropy finiteRelativeEntropy
  rw [if_pos (ker_of_mul σ h), qRel_bell σ hσ, qf_eig hh phi _ hv, qf_one_phi]
  congr 1
  rw [mul_one, Complex.ofReal_re, one_div, Real.log_inv, neg_neg]

end X6P13

-- ===== P13C =====


open Matrix ComplexConjugate
open scoped ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable

namespace X6P13

open QAlgorithms.Papers.Independent.Dependency50.P13

/-- scaled pure qubit state -/
def st (c : ℝ) (u : Bool → ℂ) : Matrix Bool Bool ℂ := ((c : ℝ) : ℂ) • vecMulVec u (star u)

lemma st_density (c : ℝ) (u : Bool → ℂ) (hc : 0 ≤ c)
    (hn : (c : ℂ) * (u false * star (u false) + u true * star (u true)) = 1) :
    QAlgorithms.IsDensityMatrix (st c u) := by
  refine ⟨(posSemidef_vecMulVec_self_star u).smul (by exact_mod_cast hc), ?_⟩
  simp only [st, Matrix.trace, Matrix.diag, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_bool, smul_eq_mul]
  rw [← hn]; ring

def vp : Bool → ℂ := fun _ => 1
def vm : Bool → ℂ := fun b => if b then -1 else 1
def vi : Bool → ℂ := fun b => if b then Complex.I else 1
def vj : Bool → ℂ := fun b => if b then -Complex.I else 1
def z0 : Bool → ℂ := fun b => if b then 0 else 1
def z1 : Bool → ℂ := fun b => if b then 1 else 0

lemma d_vp : QAlgorithms.IsDensityMatrix (st (1/2) vp) :=
  st_density _ _ (by norm_num) (by simp [vp]; norm_num)
lemma d_vm : QAlgorithms.IsDensityMatrix (st (1/2) vm) :=
  st_density _ _ (by norm_num) (by simp [vm]; norm_num)
lemma d_vi : QAlgorithms.IsDensityMatrix (st (1/2) vi) :=
  st_density _ _ (by norm_num) (by simp [vi]; norm_num)
lemma d_vj : QAlgorithms.IsDensityMatrix (st (1/2) vj) :=
  st_density _ _ (by norm_num) (by simp [vj]; norm_num)
lemma d_z0 : QAlgorithms.IsDensityMatrix (st 1 z0) :=
  st_density _ _ (by norm_num) (by simp [z0])
lemma d_z1 : QAlgorithms.IsDensityMatrix (st 1 z1) :=
  st_density _ _ (by norm_num) (by simp [z1])

lemma sep2 : QAlgorithms.Entanglement.IsSeparableDensity bellSigmaTwo := by
  refine ⟨4, fun _ => 1 / 4, ![st (1/2) vp, st (1/2) vm, st (1/2) vi, st (1/2) vj],
    ![st (1/2) vp, st (1/2) vm, st (1/2) vj, st (1/2) vi], fun _ => by norm_num,
    by norm_num, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨d_vp, d_vp⟩
    · exact ⟨d_vm, d_vm⟩
    · exact ⟨d_vi, d_vj⟩
    · exact ⟨d_vj, d_vi⟩
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    rw [sigma2_apply, bell_apply]
    rcases a1 with _ | _ <;> rcases a2 with _ | _ <;> rcases b1 with _ | _ <;>
      rcases b2 with _ | _ <;>
      simp [Fin.sum_univ_four, st, vp, vm, vi, vj, qubitPairProjector, vecMulVec_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring_nf

lemma sep1 : QAlgorithms.Entanglement.IsSeparableDensity bellSigmaOne := by
  refine ⟨6, fun _ => 1 / 6,
    ![st (1/2) vp, st (1/2) vm, st (1/2) vi, st (1/2) vj, st 1 z0, st 1 z1],
    ![st (1/2) vp, st (1/2) vm, st (1/2) vj, st (1/2) vi, st 1 z0, st 1 z1],
    fun _ => by norm_num, by norm_num, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨d_vp, d_vp⟩
    · exact ⟨d_vm, d_vm⟩
    · exact ⟨d_vi, d_vj⟩
    · exact ⟨d_vj, d_vi⟩
    · exact ⟨d_z0, d_z0⟩
    · exact ⟨d_z1, d_z1⟩
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    rw [sigma1_apply, bell_apply]
    rcases a1 with _ | _ <;> rcases a2 with _ | _ <;> rcases b1 with _ | _ <;>
      rcases b2 with _ | _ <;>
      simp [Fin.sum_univ_succ, st, vp, vm, vi, vj, z0, z1, Matrix.one_apply,
        vecMulVec_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring_nf

lemma density_of_sep {X : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (h : QAlgorithms.Entanglement.IsSeparableDensity X) : QAlgorithms.IsDensityMatrix X := by
  obtain ⟨q, w, A, B, hw, hsum, hd, rfl⟩ := h
  refine ⟨posSemidef_sum _ fun j _ => ((hd j).1.1.kronecker (hd j).2.1).smul
    (by exact_mod_cast hw j), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ j, ((w j : ℂ) • (A j ⊗ₖ B j)).trace = (w j : ℂ) := by
    intro j
    rw [Matrix.trace_smul, Matrix.trace_kronecker, (hd j).1.2, (hd j).2.2, mul_one, smul_eq_mul,
      mul_one]
  trans ∑ j, (w j : ℂ)
  · exact Finset.sum_congr rfl (fun j _ => this j)
  · exact_mod_cast hsum

end X6P13

-- ===== P13D =====


open Matrix ComplexConjugate
open scoped ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable

namespace X6P13

open QAlgorithms.Papers.Independent.Dependency50.P13

lemma re_of_nonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re := (Complex.le_def.1 h).1

/-- entries of a qubit density matrix -/
lemma psd2 (A : Matrix Bool Bool ℂ) (hA : QAlgorithms.IsDensityMatrix A) :
    0 ≤ (A false false).re ∧ 0 ≤ (A true true).re ∧
    (A false false).re + (A true true).re = 1 ∧
    ‖A false true‖ ^ 2 ≤ (A false false).re * (A true true).re ∧
    A true false = star (A false true) ∧
    A false false = ((A false false).re : ℂ) ∧ A true true = ((A true true).re : ℂ) := by
  have hH := hA.1.1
  have e1 : A true false = star (A false true) := (hH.apply true false).symm
  have e2 : A false false = ((A false false).re : ℂ) := (hH.coe_re_apply_self false).symm
  have e3 : A true true = ((A true true).re : ℂ) := (hH.coe_re_apply_self true).symm
  set p := (A false false).re
  set q := (A true true).re
  set z := A false true
  have hp : 0 ≤ p := by
    have := hA.1.diag_nonneg (i := false)
    exact re_of_nonneg this
  have hq : 0 ≤ q := by
    have := hA.1.diag_nonneg (i := true)
    exact re_of_nonneg this
  have htr : p + q = 1 := by
    have := congrArg Complex.re hA.2
    simpa [Matrix.trace, Fintype.sum_bool, p, q, add_comm] using this
  have qform : ∀ x : Bool → ℂ, 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := fun x =>
    re_of_nonneg (hA.1.dotProduct_mulVec_nonneg x)
  have h1 := qform (fun b => if b then (p : ℂ) else -z)
  have h2 := qform (fun b => if b then -star z else (q : ℂ))
  have expand : ∀ x : Bool → ℂ, star x ⬝ᵥ (A *ᵥ x) =
      star (x false) * (A false false * x false + z * x true) +
      star (x true) * (A true false * x false + A true true * x true) := by
    intro x
    simp [dotProduct, mulVec, Fintype.sum_bool, z]
    ring
  rw [expand, e1, e2, e3] at h1 h2
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_im] at h1 h2
  refine ⟨hp, hq, htr, ?_, e1, e2, e3⟩
  rw [hz]
  nlinarith

lemma overlap2 (A B : Matrix Bool Bool ℂ) (hA : QAlgorithms.IsDensityMatrix A)
    (hB : QAlgorithms.IsDensityMatrix B) : (∑ x, ∑ y, A x y * B x y).re ≤ 1 := by
  obtain ⟨hp, hq, hpq, hz, e1, e2, e3⟩ := psd2 A hA
  obtain ⟨hr, hs, hrs, hw, f1, f2, f3⟩ := psd2 B hB
  simp only [Fintype.sum_bool]
  rw [e1, e2, e3, f1, f2, f3]
  set z := A false true
  set w := B false true
  have hz' : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hw' : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hz'] at hz
  rw [hw'] at hw
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  set p := (A false false).re
  set q := (A true true).re
  set r := (B false false).re
  set t := (B true true).re
  set s := z.re * w.re - z.im * w.im
  have hs2 : s ^ 2 ≤ (p * q) * (r * t) := by
    have : s ^ 2 ≤ (z.re ^ 2 + z.im ^ 2) * (w.re ^ 2 + w.im ^ 2) := by
      nlinarith [sq_nonneg (z.re * w.im + z.im * w.re)]
    calc s ^ 2 ≤ (z.re ^ 2 + z.im ^ 2) * (w.re ^ 2 + w.im ^ 2) := this
      _ ≤ (p * q) * (r * t) := mul_le_mul hz hw (by positivity) (by positivity)
  have hX : 0 ≤ p * t + q * r := by positivity
  have hsq : (2 * s) ^ 2 ≤ (p * t + q * r) ^ 2 := by nlinarith [sq_nonneg (p * t - q * r)]
  have h2s : 2 * s ≤ p * t + q * r := by
    by_contra hc
    push Not at hc
    nlinarith
  have h1 : (p + q) * (r + t) = 1 := by rw [hpq, hrs]; ring
  nlinarith

lemma qf_kron (A B : Matrix Bool Bool ℂ) :
    qf (A ⊗ₖ B) phi = (1 / 2 : ℂ) * ∑ x, ∑ y, A x y * B x y := by
  simp only [qf, phi, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp [Fintype.sum_prod_type, Fintype.sum_bool]
  have : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 2⁻¹ := c2
  linear_combination (A false false * B false false + A false true * B false true +
    A true false * B true false + A true true * B true true) * this

lemma qf_lin {q : ℕ} (w : Fin q → ℝ) (K : Fin q → Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (v : Bool × Bool → ℂ) :
    qf (∑ j, (w j : ℂ) • K j) v = ∑ j, (w j : ℂ) * qf (K j) v := by
  simp only [qf, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ a, ∑ b, ∑ j, (w j : ℂ) * (star (v a) * K j a b * v b) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = ∑ a, ∑ j, ∑ b, (w j : ℂ) * (star (v a) * K j a b * v b) := by
        apply Finset.sum_congr rfl; intro a _
        exact Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ b, (w j : ℂ) * (star (v a) * K j a b * v b) := Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.mul_sum]

lemma qf_sep {σ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (h : QAlgorithms.Entanglement.IsSeparableDensity σ) : (qf σ phi).re ≤ 1 / 2 := by
  obtain ⟨q, w, A, B, hw, hsum, hd, rfl⟩ := h
  rw [qf_lin, Complex.re_sum]
  calc ∑ j, ((w j : ℂ) * qf (A j ⊗ₖ B j) phi).re ≤ ∑ j, w j * (1 / 2) := by
        apply Finset.sum_le_sum; intro j _
        rw [Complex.re_ofReal_mul, qf_kron]
        apply mul_le_mul_of_nonneg_left _ (hw j)
        have := overlap2 (A j) (B j) (hd j).1 (hd j).2
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        linarith
    _ = 1 / 2 := by rw [← Finset.sum_mul, hsum, one_mul]

lemma co_zero {σ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hH : σ.IsHermitian)
    (hk : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker bellState.mulVecLin) (i : Bool × Bool)
    (hi : hH.eigenvalues i = 0) : co hH phi i = 0 := by
  set u := ⇑(hH.eigenvectorBasis i)
  have hu : σ *ᵥ u = 0 := by
    rw [hH.mulVec_eigenvectorBasis, hi, zero_smul]
  have hb : bellState *ᵥ u = 0 := by
    have := hk (show u ∈ LinearMap.ker σ.mulVecLin by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hu)
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have h0 := congrFun hb (false, false)
  rw [bell_eq] at h0
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h0
  have hc : phi (false, false) ≠ 0 := by
    simp [phi]
  have hsum : ∑ b, star (phi b) * u b = 0 := by
    have : phi (false, false) * ∑ b, star (phi b) * u b = 0 := by
      rw [Finset.mul_sum]; rw [← h0]
      apply Finset.sum_congr rfl; intro b _; ring
    exact (mul_eq_zero.1 this).resolve_left hc
  have : co hH phi i = star (∑ b, star (phi b) * u b) := by
    simp only [co, dotProduct, star_sum, star_mul, star_star, Pi.star_apply]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [this, hsum, star_zero]

lemma qf_pos {A : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hA : A.PosSemidef)
    (v : Bool × Bool → ℂ) (hv : qf 1 v = 1)
    (hker : ∀ i, hA.1.eigenvalues i = 0 → co hA.1 v i = 0) : 0 < (qf A v).re := by
  have hsum : ∑ i, ‖co hA.1 v i‖ ^ 2 = 1 := by
    have := congrArg Complex.re (qf_one_eq hA.1 v)
    rw [hv] at this
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at this
    exact this.symm
  have e2 : (qf A v).re = ∑ i, ‖co hA.1 v i‖ ^ 2 * hA.1.eigenvalues i := by
    rw [qf_self_eq hA.1, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]; ring
  rw [e2]
  obtain ⟨i, hi⟩ : ∃ i, ‖co hA.1 v i‖ ^ 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hl : 0 < hA.1.eigenvalues i := by
    rcases (hA.eigenvalues_nonneg i).lt_or_eq with h | h
    · exact h
    · exfalso; apply hi; simp [hker i h.symm]
  apply Finset.sum_pos' (fun j _ => mul_nonneg (by positivity) (hA.eigenvalues_nonneg j))
  exact ⟨i, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (by positivity) (Ne.symm hi)) hl⟩

lemma lower {σ : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (h : QAlgorithms.Entanglement.IsSeparableDensity σ) :
    ENNReal.ofReal (Real.log 2) ≤ twoQubitRelativeEntropy bellState σ := by
  have hd := density_of_sep h
  unfold twoQubitRelativeEntropy finiteRelativeEntropy
  split_ifs with hk
  · rw [qRel_bell σ hd.2]
    apply ENNReal.ofReal_le_ofReal
    have hker := co_zero hd.1.1 hk
    have h1 := log_qf_le hd.1 phi qf_one_phi hker
    have hpos := qf_pos hd.1 phi qf_one_phi hker
    have h2 : Real.log (qf σ phi).re ≤ Real.log (1 / 2) :=
      Real.log_le_log hpos (qf_sep h)
    rw [one_div, Real.log_inv] at h2
    linarith
  · exact le_top

end X6P13

open QAlgorithms.Papers.Independent.Dependency50.P13 X6P13 in
theorem solution :
    QAlgorithms.IsDensityMatrix bellState ∧
    QAlgorithms.IsDensityMatrix bellSigmaOne ∧ QAlgorithms.IsDensityMatrix bellSigmaTwo ∧
    QAlgorithms.Entanglement.IsSeparableDensity bellSigmaOne ∧
    QAlgorithms.Entanglement.IsSeparableDensity bellSigmaTwo ∧
    bellSigmaOne ≠ bellSigmaTwo ∧
    twoQubitRelativeEntropy bellState bellSigmaOne = ENNReal.ofReal (Real.log 2) ∧
    twoQubitRelativeEntropy bellState bellSigmaTwo = ENNReal.ofReal (Real.log 2) ∧
    twoQubitEntanglement bellState = ENNReal.ofReal (Real.log 2) := by
  have hbell : QAlgorithms.IsDensityMatrix bellState := by
    refine ⟨?_, bell_trace⟩
    rw [bell_eq]
    exact posSemidef_vecMulVec_self_star phi
  have d1 := density_of_sep sep1
  have d2 := density_of_sep sep2
  have r1 := rel_of_eig _ d1.1.1 d1.2 sigma1_phi bell_sigma1
  have r2 := rel_of_eig _ d2.1.1 d2.2 sigma2_phi bell_sigma2
  refine ⟨hbell, d1, d2, sep1, sep2, ?_, r1, r2, ?_⟩
  · intro h
    have := congrFun (congrFun h (false, true)) (false, true)
    rw [sigma1_apply, sigma2_apply, bell_apply] at this
    simp [qubitPairProjector] at this
  · apply le_antisymm
    · rw [← r1]
      exact iInf_le (fun s : {s : Matrix (Bool × Bool) (Bool × Bool) ℂ //
        QAlgorithms.Entanglement.IsSeparableDensity s} =>
          twoQubitRelativeEntropy bellState s.val) ⟨bellSigmaOne, sep1⟩
    · exact le_iInf fun s => lower s.2

