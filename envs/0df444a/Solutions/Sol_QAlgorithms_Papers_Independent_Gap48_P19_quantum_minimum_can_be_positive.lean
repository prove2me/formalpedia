-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P19.quantum_minimum_can_be_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:12:31.504992+00:00
-- url     : https://prove2.me/submissions/0263f305-525f-454d-aed8-3c93afb77c35

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19
namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The Bell density matrix. -/
def S170I_P : Mat (Bool × Bool) := fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0

lemma S170I_quad {n : ℕ} (e : Mat ((Bool × Bool) × Fin n)) (φ : Bool × Bool → ℂ) (l : Fin n) :
    star (fun z : (Bool × Bool) × Fin n => if z.2 = l then φ z.1 else 0) ⬝ᵥ
      e *ᵥ (fun z : (Bool × Bool) × Fin n => if z.2 = l then φ z.1 else 0) =
    ∑ x, ∑ y, star (φ x) * e (x, l) (y, l) * φ y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]

lemma S170I_kill {n : ℕ} (e : Mat ((Bool × Bool) × Fin n)) (he : e.PosSemidef)
    (htr : traceRight e = S170I_P) (φ : Bool × Bool → ℂ)
    (hφ : ∑ x, ∑ y, star (φ x) * S170I_P x y * φ y = 0) (l : Fin n) (r : (Bool × Bool) × Fin n) :
    ∑ y, e r (y, l) * φ y = 0 := by
  set v : Fin n → (Bool × Bool) × Fin n → ℂ := fun l z => if z.2 = l then φ z.1 else 0 with hv
  have hq : ∀ l, 0 ≤ star (v l) ⬝ᵥ e *ᵥ (v l) := fun l => he.dotProduct_mulVec_nonneg _
  have hsum : ∑ l, star (v l) ⬝ᵥ e *ᵥ (v l) = 0 := by
    simp only [hv, S170I_quad]
    rw [← hφ, ← htr]
    simp only [traceRight, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  have hl := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => hq l).1 hsum l (Finset.mem_univ _)
  have hz := (he.dotProduct_mulVec_zero_iff (v l)).1 hl
  have := congrFun hz r
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hv, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
  rw [Fintype.sum_prod_type]; exact this

lemma S170I_factor {n : ℕ} (e : Mat ((Bool × Bool) × Fin n)) (he : e.PosSemidef)
    (htr : traceRight e = S170I_P) (x : Bool × Bool) (l : Fin n) (y : Bool × Bool) (l' : Fin n) :
    e (x, l) (y, l') = S170I_P x y * traceLeft e l l' := by
  have k := S170I_kill e he htr
  have c1 : ∀ r l, e r ((false, true), l) = 0 := by
    intro r l
    have := k (fun x => if x = (false, true) then 1 else 0)
      (by simp [S170I_P, Fintype.sum_prod_type]) l r
    simpa [Fintype.sum_prod_type] using this
  have c2 : ∀ r l, e r ((true, false), l) = 0 := by
    intro r l
    have := k (fun x => if x = (true, false) then 1 else 0)
      (by simp [S170I_P, Fintype.sum_prod_type]) l r
    simpa [Fintype.sum_prod_type] using this
  have c3 : ∀ r l, e r ((false, false), l) = e r ((true, true), l) := by
    intro r l
    have := k (fun x => if x = (false, false) then 1 else if x = (true, true) then -1 else 0)
      (by norm_num [S170I_P, Fintype.sum_prod_type]) l r
    simp [Fintype.sum_prod_type] at this
    linear_combination this
  have hh : ∀ a b, e a b = star (e b a) := fun a b => (he.1.apply a b).symm
  set t := e ((false, false), l) ((false, false), l')
  have d1 : e ((true, true), l) ((true, true), l') = t := by
    rw [← c3, hh, ← c3, ← hh]
  have d2 : e ((false, false), l) ((true, true), l') = t := by rw [← c3]
  have d3 : e ((true, true), l) ((false, false), l') = t := by rw [hh, ← c3, ← hh]
  have r1 : ∀ c, e ((false, true), l) c = 0 := fun c => by rw [hh, c1, star_zero]
  have r2 : ∀ c, e ((true, false), l) c = 0 := fun c => by rw [hh, c2, star_zero]
  have htl : traceLeft e l l' = 2 * t := by
    simp only [traceLeft, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [d1, r1, r2]; ring
  rw [htl]
  rcases x with ⟨_ | _, _ | _⟩ <;> rcases y with ⟨_ | _, _ | _⟩ <;>
    simp [S170I_P, c1, c2, r1, r2, d1, d2, d3, t]

/-- the kronecker map by a projector as a non-unital star algebra hom -/
def S170I_kronHom {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
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

lemma S170I_ent_kron {R I : Type*} [Fintype R] [Fintype I] [DecidableEq R] [DecidableEq I]
    (Pc : Matrix R R ℂ) (hsq : Pc * Pc = Pc) (hh : Pcᴴ = Pc)
    (sigma : Matrix I I ℂ) (hs : sigma.IsHermitian) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy (Matrix.kronecker Pc sigma) =
      -(Pc.trace * (cfc (fun x : ℝ => x * Real.log x) sigma).trace).re := by
  have hcont : Continuous (fun x : ℝ => x * Real.log x) := Real.continuous_mul_log
  have hsa : IsSelfAdjoint sigma := hs
  let φ := S170I_kronHom (I := I) Pc hsq hh
  have hφ : Continuous φ := by
    show Continuous fun Y : Matrix I I ℂ => Matrix.kronecker Pc Y
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_const.mul ((continuous_apply j.2).comp (continuous_apply i.2))
  have hφa : IsSelfAdjoint (φ sigma) := by
    show star (φ sigma) = φ sigma
    rw [← map_star, hsa.star_eq]
  have key := NonUnitalStarAlgHom.map_cfcₙ φ (fun x : ℝ => x * Real.log x) sigma
    hcont.continuousOn (by simp) hφ hsa hφa
  rw [cfcₙ_eq_cfc hcont.continuousOn (by simp), cfcₙ_eq_cfc hcont.continuousOn (by simp)] at key
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  have : φ sigma = Matrix.kronecker Pc sigma := rfl
  rw [← this, ← key]
  show -(Matrix.kronecker Pc (cfc (fun x : ℝ => x * Real.log x) sigma)).trace.re = _
  erw [Matrix.trace_kronecker]

lemma S170I_ent_half {I : Type*} [Fintype I] [DecidableEq I] (tau : Matrix I I ℂ) (hs : tau.IsHermitian)
    (htr : tau.trace = 1) :
    -((cfc (fun x : ℝ => x * Real.log x) ((1 / 2 : ℂ) • tau)).trace).re =
      (1 / 2) * QAlgorithms.Papers.Independent.Information100.P56.entropy tau + Real.log 2 / 2 := by
  have hsa : IsSelfAdjoint tau := hs
  have e1 : (1 / 2 : ℂ) • tau = (1 / 2 : ℝ) • tau := by
    rw [← Complex.coe_smul]; norm_num
  have hf : (fun x : ℝ => (1 / 2 : ℝ) • x * Real.log ((1 / 2 : ℝ) • x)) =
      fun x => (1 / 2 : ℝ) * (x * Real.log x) - (Real.log 2 / 2) * x := by
    funext x
    simp only [smul_eq_mul]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [show 1 / 2 * x = x / 2 by ring, Real.log_div hx two_ne_zero]; ring
  rw [e1, ← cfc_comp_smul (1 / 2 : ℝ) (fun x : ℝ => x * Real.log x) tau
    Real.continuous_mul_log.continuousOn, hf]
  have c1 : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * (x * Real.log x)) (spectrum ℝ tau) :=
    (continuous_const.mul Real.continuous_mul_log).continuousOn
  have c2 : ContinuousOn (fun x : ℝ => (Real.log 2 / 2) * x) (spectrum ℝ tau) :=
    (continuous_const.mul continuous_id).continuousOn
  rw [cfc_sub _ _ tau c1 c2, cfc_const_mul (1 / 2 : ℝ) (fun x : ℝ => x * Real.log x) tau
    Real.continuous_mul_log.continuousOn, cfc_const_mul (Real.log 2 / 2) (fun x : ℝ => x) tau
    continuous_id.continuousOn, cfc_id' ℝ tau]
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, htr]
  simp [Complex.sub_re]
  rw [show (Complex.log 2).re = Real.log 2 by simp [Complex.log_re]]
  ring

lemma S170I_Psq : S170I_P * S170I_P = S170I_P := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, S170I_P] <;> norm_num

lemma S170I_Ph : S170I_Pᴴ = S170I_P := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;>
    simp [Matrix.conjTranspose_apply, S170I_P]

lemma S170I_Ptr : S170I_P.trace = 1 := by
  simp [Matrix.trace, Fintype.sum_prod_type, S170I_P]

lemma S170I_herm_half {I : Type*} [Fintype I] (tau : Matrix I I ℂ) (hs : tau.IsHermitian) :
    ((1 / 2 : ℂ) • tau).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hs.eq]
  congr 1
  simp

lemma S170I_cmi {n : ℕ} (e : Mat ((Bool × Bool) × Fin n)) (he : e.PosSemidef) (htr1 : e.trace = 1)
    (htr : traceRight e = S170I_P) : extensionQuantumCMI e = 2 * Real.log 2 := by
  set tau := traceLeft e with htau
  have hτh : tau.IsHermitian := by
    ext l l'
    simp only [htau, traceLeft, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact he.1.apply _ _
  have hτtr : tau.trace = 1 := by
    rw [← htr1]
    simp only [htau, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hfac := S170I_factor e he htr
  have he_eq : e = Matrix.kronecker S170I_P tau := by
    ext ⟨x, l⟩ ⟨y, l'⟩
    rw [hfac]; rfl
  have hAL : marginalAL e = Matrix.kronecker (1 : Matrix Bool Bool ℂ) ((1 / 2 : ℂ) • tau) := by
    ext ⟨a, l⟩ ⟨a', l'⟩
    simp only [marginalAL, hfac, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    rcases a with _ | _ <;> rcases a' with _ | _ <;> simp [Fintype.sum_bool, S170I_P] <;> ring
  have hBL : marginalBL e = Matrix.kronecker (1 : Matrix Bool Bool ℂ) ((1 / 2 : ℂ) • tau) := by
    ext ⟨a, l⟩ ⟨a', l'⟩
    simp only [marginalBL, hfac, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    rcases a with _ | _ <;> rcases a' with _ | _ <;> simp [Fintype.sum_bool, S170I_P] <;> ring
  have h1 : (1 : Matrix Bool Bool ℂ) * 1 = 1 := Matrix.one_mul 1
  have h1h : (1 : Matrix Bool Bool ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hS1 := S170I_ent_kron (1 : Matrix Bool Bool ℂ) h1 h1h _ (S170I_herm_half tau hτh)
  have hSP := S170I_ent_kron S170I_P S170I_Psq S170I_Ph tau hτh
  have hhalf := S170I_ent_half tau hτh hτtr
  have htr1' : (1 : Matrix Bool Bool ℂ).trace = 2 := by simp [Matrix.trace]
  unfold extensionQuantumCMI
  rw [hAL, hBL, ← htau, he_eq, hS1, hSP, htr1', S170I_Ptr, one_mul]
  have e2 : ∀ z : ℂ, -((2 : ℂ) * z).re = 2 * (-z.re) := fun z => by simp
  rw [e2, hhalf]
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  ring

lemma S170I_vec : ∃ ψ : Bool × Bool → ℂ, S170I_P = Matrix.vecMulVec ψ (star ψ) := by
  refine ⟨fun x => if x.1 = x.2 then ((Real.sqrt 2 : ℂ))⁻¹ else 0, ?_⟩
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [S170I_P, Matrix.vecMulVec_apply, Pi.star_apply]
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases c with _ | _ <;> rcases d with _ | _ <;> simp [hs]

end

end QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    ∃ rho : Mat (Bool × Bool), IsDensityMatrix rho ∧
      ∃ m : ℝ, 0 < m ∧ IsLeast (quantumScores rho) m := by
  obtain ⟨ψ, hψ⟩ := S170I_vec
  refine ⟨S170I_P, ⟨hψ ▸ Matrix.posSemidef_vecMulVec_self_star ψ, S170I_Ptr⟩, 2 * Real.log 2,
    by positivity, ?_, ?_⟩
  · let e0 : Mat ((Bool × Bool) × Fin 1) := Matrix.vecMulVec (fun z => ψ z.1) (star fun z => ψ z.1)
    have he0 : e0 = Matrix.kronecker S170I_P (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      ext ⟨x, l⟩ ⟨y, l'⟩
      rw [hψ]
      simp [e0, Matrix.vecMulVec_apply, Fin.fin_one_eq_zero l, Fin.fin_one_eq_zero l']
    have hpsd : e0.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
    have htr1 : e0.trace = 1 := by
      rw [he0]; erw [Matrix.trace_kronecker]; rw [S170I_Ptr]; simp
    have htr : traceRight e0 = S170I_P := by
      ext x y
      simp [traceRight, he0]
    exact ⟨⟨1, e0⟩, ⟨Nat.one_pos, ⟨hpsd, htr1⟩, htr⟩, S170I_cmi e0 hpsd htr1 htr⟩
  · rintro r ⟨⟨k, e⟩, ⟨_, ⟨hpsd, htr1⟩, htr⟩, rfl⟩
    exact (S170I_cmi e hpsd htr1 htr).ge

