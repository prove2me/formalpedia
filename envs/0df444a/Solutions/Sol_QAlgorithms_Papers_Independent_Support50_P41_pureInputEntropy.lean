-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.pureInputEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:38:09.889022+00:00
-- url     : https://prove2.me/submissions/e5ecebac-71ea-4c5c-98e3-8d7a28d27513

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== KFE =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

-- The next four lemmas are adapted from the accepted proof of
-- Dependency50.P48.privateInformationDominates (another agent on this account, `g53c_*`).
lemma pk_proj_sq {I : Type*} [Fintype I] (w : I → ℂ) (hw : ∑ i, conj (w i) * w i = 1) :
    (Matrix.of fun a b => w a * conj (w b)) * (Matrix.of fun a b => w a * conj (w b)) =
      Matrix.of fun a b => w a * conj (w b) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have : ∑ x, w a * conj (w x) * (w x * conj (w b)) = w a * conj (w b) * ∑ x, conj (w x) * w x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [this, hw, mul_one]

lemma pk_proj_herm {I : Type*} [Fintype I] (w : I → ℂ) :
    (Matrix.of fun a b => w a * conj (w b))ᴴ = Matrix.of fun a b => w a * conj (w b) := by
  ext a b
  simp [Matrix.conjTranspose_apply, mul_comm]

lemma pk_proj_sqrt {I : Type*} [Fintype I] [DecidableEq I] (w : I → ℂ)
    (hw : ∑ i, conj (w i) * w i = 1) :
    cfc Real.sqrt (Matrix.of fun a b => w a * conj (w b)) = Matrix.of fun a b => w a * conj (w b) := by
  set M : Matrix I I ℂ := Matrix.of fun a b => w a * conj (w b) with hM
  have hsa : IsSelfAdjoint M := pk_proj_herm w
  have h0 : cfc (fun x : ℝ => x * x) M = cfc (fun x : ℝ => x) M := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M, cfc_id' ℝ M, pk_proj_sq w hw]
  have h1 := eqOn_of_cfc_eq_cfc h0
  conv_rhs => rw [← cfc_id' ℝ M]
  apply cfc_congr
  intro x hx
  have hx2 : x * x = x := h1 hx
  have : x = 0 ∨ x = 1 := by
    have : x * (x - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · left; exact h
    · right; linarith
  rcases this with rfl | rfl <;> simp

/-- the kronecker map by a projector as a non-unital star algebra hom -/
def pk_kronHom {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
    (Pc : Matrix R R ℂ) (hsq : Pc * Pc = Pc) (hh : Pcᴴ = Pc) :
    Matrix I I ℂ →⋆ₙₐ[ℂ] Matrix (R × I) (R × I) ℂ where
  toFun Y := Matrix.kronecker Pc Y
  map_smul' c Y := by
    simp only [MonoidHom.id_apply]
    exact Matrix.kronecker_smul c Pc Y
  map_zero' := Matrix.kronecker_zero _
  map_add' Y Z := Matrix.kronecker_add Pc Y Z
  map_mul' Y Z := by
    show Matrix.kronecker Pc (Y * Z) = Matrix.kronecker Pc Y * Matrix.kronecker Pc Z
    have := Matrix.mul_kronecker_mul Pc Pc Y Z
    rw [hsq] at this
    exact this
  map_star' Y := by
    have hpc : ∀ a c, Pc a c = star (Pc c a) := fun a c => by
      have := congrFun (congrFun hh a) c
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    ext ⟨a, b⟩ ⟨c, d⟩
    show Pc a c * (star Y) b d = star (Pc c a * Y d b)
    rw [Matrix.star_apply, star_mul', hpc a c]

lemma pk_entropy_kron {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
    (Pc : Matrix R R ℂ) (hsq : Pc * Pc = Pc) (hh : Pcᴴ = Pc) (htr : Pc.trace = 1)
    (sigma : Matrix I I ℂ) (hs : sigma.IsHermitian) :
    vnEntropy (Matrix.kronecker Pc sigma) = vnEntropy sigma := by
  have hcont : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
    have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
      funext x; rw [Real.logb]; ring
    rw [this]; exact Real.continuous_mul_log.div_const _
  have hsa : IsSelfAdjoint sigma := hs
  let φ := pk_kronHom (I := I) Pc hsq hh
  have hφ : Continuous φ := by
    show Continuous fun Y : Matrix I I ℂ => Matrix.kronecker Pc Y
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j.2).comp (continuous_apply i.2))
  have hφa : IsSelfAdjoint (φ sigma) := by
    show star (φ sigma) = φ sigma
    rw [← map_star, hsa.star_eq]
  have key := NonUnitalStarAlgHom.map_cfcₙ φ (fun x : ℝ => x * Real.logb 2 x) sigma
    hcont.continuousOn (by simp) hφ hsa hφa
  rw [cfcₙ_eq_cfc hcont.continuousOn (by simp), cfcₙ_eq_cfc hcont.continuousOn (by simp)] at key
  unfold vnEntropy
  have : φ sigma = Matrix.kronecker Pc sigma := rfl
  rw [← this, ← key]
  show -(Matrix.kronecker Pc (cfc (fun x : ℝ => x * Real.logb 2 x) sigma)).trace.re = _
  erw [Matrix.trace_kronecker]
  rw [htr, one_mul]

lemma kraus_smul {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    krausApply E (c • M) = c • krausApply E M := by
  simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma kraus_herm {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M.IsHermitian) : (krausApply E M).IsHermitian := by
  unfold krausApply
  refine isSelfAdjoint_sum _ fun k _ => ?_
  exact Matrix.isHermitian_mul_mul_conjTranspose (E k) hM

theorem pure_input {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    entropyExchange Phi (pureDensity v) = vnEntropy (Phi (pureDensity v)) := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  have hn : ∑ i, conj (v i) * v i = 1 := by
    have h1 : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h1
    have : ∑ i, conj (v i) * v i = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.conj_mul']
    rw [this, h1]; simp
  unfold entropyExchange
  simp only
  set e := Fintype.equivFin (Fin d)
  set w : Fin (Fintype.card (Fin d)) → ℂ := fun i => v (e.symm i)
  have hw : ∑ i, conj (w i) * w i = 1 := by
    rw [← hn]; exact e.symm.sum_comp (fun i => conj (v i) * v i)
  have hrho : (fun i j => pureDensity v (e.symm i) (e.symm j) :
      Matrix (Fin (Fintype.card (Fin d))) (Fin (Fintype.card (Fin d))) ℂ) =
      Matrix.of fun a b => w a * conj (w b) := by
    ext i j; simp [pureDensity, w]
  rw [hrho]
  have hpsi : ∀ inst : DecidableEq (Fin (Fintype.card (Fin d))), (WithLp.toLp 2 fun z : Fin d × Fin d =>
      @canonicalPurification _ _ inst (Matrix.of fun a b => w a * conj (w b)) (e z.1, e z.2) :
        EuclideanSpace ℂ (Fin d × Fin d)) = WithLp.toLp 2 fun z => conj (v z.1) * v z.2 := by
    intro inst
    congr 1
    funext z
    simp only [canonicalPurification]
    rw [pk_proj_sqrt w hw]
    simp [w, mul_comm]
  rw [hpsi]
  set Pc : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b => conj (v a) * conj (conj (v b))
  have hkron : pureDensity (WithLp.toLp 2 fun z : Fin d × Fin d => conj (v z.1) * v z.2 :
      EuclideanSpace ℂ (Fin d × Fin d)) = Matrix.kronecker Pc (pureDensity v) := by
    ext ⟨a, b⟩ ⟨c, f⟩
    simp [pureDensity, Pc, Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  have hid : idTensorSuperop (R := Fin d) Phi (Matrix.kronecker Pc (pureDensity v)) =
      Matrix.kronecker Pc (Phi (pureDensity v)) := by
    ext ⟨a, b⟩ ⟨c, f⟩
    simp only [idTensorSuperop, Matrix.of_apply]
    have : (Matrix.of fun i i' => Matrix.kronecker Pc (pureDensity v) (a, i) (c, i')) =
        Pc a c • pureDensity v := by
      ext i i'; simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
    rw [this, hE, hE, kraus_smul]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hkron, hid]
  have hc : ∑ i, conj (conj (v i)) * conj (v i) = 1 := by
    rw [← hn]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  apply pk_entropy_kron Pc (pk_proj_sq _ hc) (pk_proj_herm _)
  · simp only [Matrix.trace, Matrix.diag, Pc, Matrix.of_apply]
    rw [← hc]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  · rw [hE]
    apply kraus_herm
    ext i j; simp [pureDensity, mul_comm]

end X4KF

-- ===== KFSol4 =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFSol4 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem solution {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    entropyExchange Phi (pureDensity v) = vnEntropy (Phi (pureDensity v)) :=
  X4KF.pure_input Phi hPhi v hv

end

#print axioms solution
