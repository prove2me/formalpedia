-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.pqc_randomization_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:30.033004+00:00
-- url     : https://prove2.me/submissions/b10e7ff9-9265-448b-bf7e-5821f3dcf73b

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

theorem solution (n a N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)) :
    PQC S E anc rho0 ↔ ExactSourceRandomization S E anc rho0 := Iff.rfl
