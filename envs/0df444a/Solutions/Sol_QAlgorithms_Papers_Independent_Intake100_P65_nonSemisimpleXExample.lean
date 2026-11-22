-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.nonSemisimpleXExample
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T21:08:45.344945+00:00
-- url     : https://prove2.me/submissions/ac50a372-aa89-4720-979f-d9df057523a2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

def AuxNS_x (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R := !![0, 1/4; -1/4, 1/2]
def AuxNS_E (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R := !![1,0;0,0]
def AuxNS_S (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R := !![1,0;0,-1]

def AuxNS_gen (R : Type*) [Field R] : BMWLetter 2 → Matrix (Fin 2) (Fin 2) R
  | .s _ => AuxNS_S R
  | .e _ => AuxNS_E R
  | .x i => if i.val = 0 then AuxNS_x R else -AuxNS_x R

def AuxNS_free (R : Type*) [Field R] : FreeAlgebra R (BMWLetter 2) →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  FreeAlgebra.lift R (AuxNS_gen R)

lemma AuxNS_fS (R : Type*) [Field R] : AuxNS_free R (freeS R 2 0) = AuxNS_S R := by
  simp [freeS, AuxNS_free, AuxNS_gen]
lemma AuxNS_fE (R : Type*) [Field R] : AuxNS_free R (freeE R 2 0) = AuxNS_E R := by
  simp [freeE, AuxNS_free, AuxNS_gen]
lemma AuxNS_fX0 (R : Type*) [Field R] : AuxNS_free R (freeX R 2 0) = AuxNS_x R := by
  simp [freeX, AuxNS_free, AuxNS_gen]
lemma AuxNS_fX1 (R : Type*) [Field R] : AuxNS_free R (freeX R 2 1) = -AuxNS_x R := by
  simp [freeX, AuxNS_free, AuxNS_gen]

lemma AuxNS_two (R : Type*) [Field R] [Invertible (2 : R)] : (2 : R) ≠ 0 := Invertible.ne_zero 2

lemma AuxNS_sq (R : Type*) [Field R] [Invertible (2 : R)] :
    AuxNS_x R * AuxNS_x R = (1/2 : R) • AuxNS_x R - (1/16 : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h2 := AuxNS_two R
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [AuxNS_x, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

lemma AuxNS_pow (R : Type*) [Field R] [Invertible (2 : R)] (omega : ℕ → R)
    (hzero : omega 0 = 1) (hone : omega 1 = 0)
    (hrec : ∀ a, omega (a+2) = (1/2 : R) * omega (a+1) - (1/16 : R) * omega a) :
    ∀ a, (AuxNS_x R ^ a) 0 0 = omega a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a, ih with
    | 0, _ => simp [hzero]
    | 1, _ => simp [hone, AuxNS_x]
    | b+2, ih =>
      rw [hrec, pow_succ, pow_succ, mul_assoc, AuxNS_sq, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_smul, mul_one, ← pow_succ]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [ih b (by omega), ih (b+1) (by omega)]

lemma AuxNS_EME (R : Type*) [Field R] (M : Matrix (Fin 2) (Fin 2) R) :
    AuxNS_E R * M * AuxNS_E R = M 0 0 • AuxNS_E R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [AuxNS_E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma AuxNS_rel (R : Type*) [Field R] [Invertible (2 : R)] (omega : ℕ → R)
    (hzero : omega 0 = 1) (hone : omega 1 = 0)
    (hrec : ∀ a, omega (a+2) = (1/2 : R) * omega (a+1) - (1/16 : R) * omega a) :
    ∀ ⦃a b⦄, BMWRel R omega 2 a b → AuxNS_free R a = AuxNS_free R b := by
  have h2 := AuxNS_two R
  intro a b h
  cases h with
  | involution i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_pow, AuxNS_fS, map_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [AuxNS_S, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  | braidFar i j hi hj hd => omega
  | braidNear i hi => omega
  | sx i j hi hj hji hji1 => omega
  | idempotent i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_pow, map_mul, AuxNS_fE, AlgHom.commutes, hzero, map_one, one_mul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [AuxNS_E, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  | seFar i j hi hj hd => omega
  | eeFar i j hi hj hd => omega
  | ex i j hi hj hji hji1 => omega
  | xxCommute i j hi hj =>
    simp only [map_mul, freeX, AuxNS_free, FreeAlgebra.lift_ι_apply, dif_pos hi, dif_pos hj, AuxNS_gen]
    split_ifs <;> simp
  | skeinLeft i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_sub, map_sub, map_mul, map_mul, AuxNS_fS, AuxNS_fE, AuxNS_fX0, map_one,
      show (0:ℕ)+1 = 1 from rfl, AuxNS_fX1]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [AuxNS_S, AuxNS_E, AuxNS_x, Matrix.mul_apply, Fin.sum_univ_two] <;> (try ring) <;> rw [inv_mul_cancel₀ h2]
  | skeinRight i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_sub, map_sub, map_mul, map_mul, AuxNS_fS, AuxNS_fE, AuxNS_fX0, map_one,
      show (0:ℕ)+1 = 1 from rfl, AuxNS_fX1]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [AuxNS_S, AuxNS_E, AuxNS_x, Matrix.mul_apply, Fin.sum_univ_two] <;> (try ring) <;> rw [inv_mul_cancel₀ h2]
  | unwrap a ha hn =>
    rw [map_mul, map_mul, map_pow, map_mul, AuxNS_fE, AuxNS_fX0, AlgHom.commutes, AuxNS_EME,
      AuxNS_pow R omega hzero hone hrec, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  | es i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, AuxNS_fS, AuxNS_fE]
    ext i j; fin_cases i <;> fin_cases j <;> simp [AuxNS_S, AuxNS_E, Matrix.mul_apply, Fin.sum_univ_two]
  | se i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, AuxNS_fS, AuxNS_fE]
    ext i j; fin_cases i <;> fin_cases j <;> simp [AuxNS_S, AuxNS_E, Matrix.mul_apply, Fin.sum_univ_two]
  | tangleLeft i hi => omega
  | tangleRight i hi => omega
  | tangleLeftReverse i hi => omega
  | tangleRightReverse i hi => omega
  | untwistLeft i hi => omega
  | untwistRight i hi => omega
  | antisymLeft i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, map_add, AuxNS_fE, AuxNS_fX0, show (0:ℕ)+1 = 1 from rfl, AuxNS_fX1, map_zero]
    simp
  | antisymRight i hi =>
    obtain rfl : i = 0 := by omega
    rw [map_mul, map_add, AuxNS_fE, AuxNS_fX0, show (0:ℕ)+1 = 1 from rfl, AuxNS_fX1, map_zero]
    simp


lemma AuxNS_irr (R : Type*) [Field R] [Invertible (2 : R)] (U : Submodule R (Fin 2 → R))
    (hE : ∀ v ∈ U, Matrix.mulVec (AuxNS_E R) v ∈ U) (hX : ∀ v ∈ U, Matrix.mulVec (AuxNS_x R) v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have h2 := AuxNS_two R
  have h4 : (4 : R) ≠ 0 := by
    have := mul_ne_zero h2 h2; norm_num at this; exact this
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have key : ![(1:R), 0] ∈ U → U = ⊤ := by
    intro h0
    have h1 : ![(0:R), 1] ∈ U := by
      have := U.smul_mem (-4 : R) (hX _ h0)
      convert this using 1
      ext i; fin_cases i <;> simp [AuxNS_x, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      all_goals simp [div_self h4]
    rw [eq_top_iff]
    intro w _
    have : w = w 0 • ![(1:R), 0] + w 1 • ![(0:R), 1] := by
      ext i; fin_cases i <;> simp
    rw [this]
    exact U.add_mem (U.smul_mem _ h0) (U.smul_mem _ h1)
  apply key
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv0; ext i; fin_cases i <;> simp [h0, h1]
    have := U.smul_mem (4 / v 1) (hE _ (hX _ hv))
    convert this using 1
    ext i; fin_cases i <;> simp [AuxNS_x, AuxNS_E, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    field_simp
    all_goals simp [div_self h4]
  · have := U.smul_mem (v 0)⁻¹ (hE _ hv)
    convert this using 1
    ext i; fin_cases i <;> simp [AuxNS_E, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]

theorem nonSemisimpleXExample (R : Type u) [Field R] [IsAlgClosed R]
    [Invertible (2 : R)] (omega : ℕ → R)
    (hzero : omega 0 = 1) (hone : omega 1 = 0)
    (hrec : ∀ a, omega (a+2) = (1/2 : R) * omega (a+1) - (1/16 : R) * omega a)
    (ha : OmegaAdmissible omega) :
    ∀ r : ℕ, r = 2 ∨ r = 3 →
      let roots : Fin r → R := fun i => if i.val < 2 then 1/4 else -1/2
      let x : Matrix (Fin 2) (Fin 2) R := !![0, 1/4; -1/4, 1/2]
      ∃ rho : Cyclotomic R omega .degenerate r roots 2 →ₐ[R]
          Module.End R (Fin 2 → R),
        IrreducibleRepresentation rho ∧
        rho (ce R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,0] ∧
        rho (cg R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,-1] ∧
        rho (cy R omega .degenerate r roots 2) = Matrix.toLin' x ∧
        rho (toCycl R omega .degenerate r roots 2 (affineX R omega 2 1)) =
          Matrix.toLin' (-x) ∧
        x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R) ≠ 0 ∧
        (x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R))^2 = 0 := by
  have h2 := AuxNS_two R
  have h4 : (4 : R) ≠ 0 := by
    have := mul_ne_zero h2 h2; norm_num at this; exact this
  intro r hr roots x
  let φ : AffineBMW R omega 2 →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
    RingQuot.liftAlgHom R ⟨AuxNS_free R, AuxNS_rel R omega hzero hone hrec⟩
  have hφ : ∀ a, φ (affineBMWQuotientMap R omega 2 a) = AuxNS_free R a := fun a =>
    RingQuot.liftAlgHom_mkAlgHom_apply R _ _ a
  have hX0 : φ (affineX R omega 2 0) = AuxNS_x R := by
    rw [affineX, hφ, AuxNS_fX0]
  have hX1 : φ (affineX R omega 2 1) = -AuxNS_x R := by
    rw [affineX, hφ, AuxNS_fX1]
  have hE0 : φ (affineE R omega 2 0) = AuxNS_E R := by
    rw [affineE, hφ, AuxNS_fE]
  have hS0 : φ (affineS R omega 2 0) = AuxNS_S R := by
    rw [affineS, hφ, AuxNS_fS]
  have hcyc : ∀ ⦃a b : Affine R omega .degenerate 2⦄,
      cyclRel R omega .degenerate 2 r roots a b → φ a = φ b := by
    rintro a b ⟨rfl, rfl⟩
    have hay : (ay R omega .degenerate 2 : AffineBMW R omega 2) = affineX R omega 2 0 := rfl
    show φ (List.ofFn fun i : Fin r => (affineX R omega 2 0 : AffineBMW R omega 2) -
      algebraMap R (AffineBMW R omega 2) (roots i)).prod = φ 0
    rw [map_zero, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_sub, AlgHom.commutes, hX0]
    rcases hr with rfl | rfl
    · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, roots]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [AuxNS_x, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;>
        field_simp <;> ring
    · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, roots]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [AuxNS_x, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;>
        field_simp <;> ring
  let ψ : Cyclotomic R omega .degenerate r roots 2 →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
    RingQuot.liftAlgHom R ⟨φ, hcyc⟩
  have hψ : ∀ a : AffineBMW R omega 2, ψ (toCycl R omega .degenerate r roots 2 a) = φ a :=
    fun a => RingQuot.liftAlgHom_mkAlgHom_apply R _ _ a
  let rho : Cyclotomic R omega .degenerate r roots 2 →ₐ[R] Module.End R (Fin 2 → R) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) R ≃ₐ[R] Module.End R (Fin 2 → R)).toAlgHom.comp ψ
  have hrho : ∀ a : AffineBMW R omega 2,
      rho (toCycl R omega .degenerate r roots 2 a) = Matrix.toLin' (φ a) := by
    intro a
    show Matrix.toLinAlgEquiv' (ψ (toCycl R omega .degenerate r roots 2 a)) = _
    rw [hψ]; rfl
  have hce : rho (ce R omega .degenerate r roots 2 0) = Matrix.toLin' (AuxNS_E R) := by
    rw [← hE0]; exact hrho _
  have hcy : rho (cy R omega .degenerate r roots 2) = Matrix.toLin' (AuxNS_x R) := by
    rw [← hX0]; exact hrho _
  refine ⟨rho, ⟨⟨![1, 0], by simp⟩, ?_⟩, hce, ?_, hcy, ?_, ?_, ?_⟩
  · intro U hU
    apply AuxNS_irr R U
    · intro v hv
      have := hU (ce R omega .degenerate r roots 2 0) v hv
      rwa [hce, Matrix.toLin'_apply] at this
    · intro v hv
      have := hU (cy R omega .degenerate r roots 2) v hv
      rwa [hcy, Matrix.toLin'_apply] at this
  · rw [← show φ (affineS R omega 2 0) = !![1,0;0,-1] from hS0]; exact hrho _
  · rw [hrho, hX1]; rfl
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [x] at this
    exact h4 this
  · simp only [x, pow_two]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

end QAlgorithms.Papers.Independent.Intake100.P65

end

open QAlgorithms.Papers.Independent.Renew46.P16
open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)
open QAlgorithms.Papers.Independent.Support21.P12

theorem solution (R : Type*) [Field R] [IsAlgClosed R]
    [Invertible (2 : R)] (omega : ℕ → R)
    (hzero : omega 0 = 1) (hone : omega 1 = 0)
    (hrec : ∀ a, omega (a+2) = (1/2 : R) * omega (a+1) - (1/16 : R) * omega a)
    (ha : QAlgorithms.Papers.Independent.Intake100.P65.OmegaAdmissible omega) :
    ∀ r : ℕ, r = 2 ∨ r = 3 →
      let roots : Fin r → R := fun i => if i.val < 2 then 1/4 else -1/2
      let x : Matrix (Fin 2) (Fin 2) R := !![0, 1/4; -1/4, 1/2]
      ∃ rho : Cyclotomic R omega .degenerate r roots 2 →ₐ[R]
          Module.End R (Fin 2 → R),
        IrreducibleRepresentation rho ∧
        rho (ce R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,0] ∧
        rho (cg R omega .degenerate r roots 2 0) = Matrix.toLin' !![1,0;0,-1] ∧
        rho (cy R omega .degenerate r roots 2) = Matrix.toLin' x ∧
        rho (toCycl R omega .degenerate r roots 2 (affineX R omega 2 1)) =
          Matrix.toLin' (-x) ∧
        x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R) ≠ 0 ∧
        (x - (1/4 : R) • (1 : Matrix (Fin 2) (Fin 2) R))^2 = 0 :=
  QAlgorithms.Papers.Independent.Intake100.P65.nonSemisimpleXExample R omega hzero hone hrec ha
