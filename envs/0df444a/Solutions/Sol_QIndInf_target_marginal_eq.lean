-- Prove2me | solution 1 for QIndInf.target_marginal_eq
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:18:10.877482+00:00
-- url     : https://prove2.me/submissions/15657c6d-fdc1-4b49-95e3-9e25b9b9f8e4

import Mathlib
import Definitions.Def_QIndInf_target
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace QIndInf
open QAlgorithms QAlgorithms.CopyMeasurements
open scoped Matrix

lemma instrument_trace_sum {R O : Type*} [Fintype R] [DecidableEq R] [Fintype O]
    (J : QuantumInstrument R O) (Y : Matrix R R ℂ) :
    ∑ o, Matrix.trace (instrumentBranch J o Y) = Matrix.trace Y := by
  have hc (o : O) (j : Fin (J.multiplicity o)) :
      Matrix.trace (J.kraus o j * Y * (J.kraus o j)ᴴ) =
        Matrix.trace (Y * ((J.kraus o j)ᴴ * J.kraus o j)) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle Y ((J.kraus o j)ᴴ) (J.kraus o j)).symm
  calc
    _ = Matrix.trace (Y * (∑ o,∑ j,(J.kraus o j)ᴴ * J.kraus o j)) := by
      simp only [instrumentBranch, krausApply, Matrix.trace_sum,
        Matrix.mul_sum, hc]
    _ = Matrix.trace Y := by rw [J.complete,Matrix.mul_one]

lemma partialTrace_measNext {A : Type} {n k : ℕ}
    (J : QuantumInstrument (Reg n) (Fin k))
    (Y : Matrix (A × Reg n) (A × Reg n) ℂ) :
    WildeQIT.partialTraceRight (measNext J Y) = WildeQIT.partialTraceRight Y := by
  classical
  ext a b
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, measNext,
    if_pos rfl, idTensorSuperop]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact instrument_trace_sum J (Matrix.of fun r s => Y (a,r) (b,s))

noncomputable def piSuperopLinear {R S : Type*} [Fintype R] [DecidableEq R] {m : ℕ}
    (Φ : Fin m → Superop R S) :
    Matrix (Fin m → R) (Fin m → R) ℂ →ₗ[ℂ] Matrix (Fin m → S) (Fin m → S) ℂ where
  toFun X := piSuperop Φ X
  map_add' X Y := by
    ext a b
    simp only [piSuperop, Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    simp only [piSuperop, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, Finset.mul_sum, RingHom.id_apply]

lemma partialTrace_superopTensorId_linear {A B R : Type} [Fintype R]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (A × R) (A × R) ℂ) :
    WildeQIT.partialTraceRight (superopTensorId Φ X) =
      Φ (WildeQIT.partialTraceRight X) := by
  have he : WildeQIT.partialTraceRight X =
      ∑ r : R, Matrix.of (fun a b => X (a,r) (b,r)) := by
    ext a b
    simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.sum_apply]
  rw [he,map_sum]
  ext a b
  simp only [WildeQIT.partialTraceRight, superopTensorId, Matrix.of_apply, Matrix.sum_apply]

lemma partialTrace_smul {A R : Type} [Fintype R]
    (c : ℂ) (X : Matrix (A × R) (A × R) ℂ) :
    WildeQIT.partialTraceRight (c • X) = c • WildeQIT.partialTraceRight X := by
  ext a b
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]

end QIndInf
open QIndInf
open QAlgorithms.CopyMeasurements

theorem solution {n j : ℕ} (ρ : QuantumProcess n) {k : Fin (j + 1) → ℕ}
    (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) :
    WildeQIT.partialTraceRight (target ρ.state I x) = condPast ρ.state (pastInstr I) x := by
  rw [target,partialTrace_measNext,condNext,partialTrace_smul]
  have he := partialTrace_superopTensorId_linear
    (piSuperopLinear (fun l => instrumentBranch (pastInstr I l) (x l)))
    (splitLast (ρ.state (j + 1)))
  change WildeQIT.partialTraceRight
    (superopTensorId (histOp (pastInstr I) x) (splitLast (ρ.state (j + 1)))) =
      histOp (pastInstr I) x (traceLast (ρ.state (j + 1))) at he
  rw [he,ρ.consistent]
  rfl

