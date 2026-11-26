-- Prove2me | solution 1 for Section5DecoderLayout.integer_matrix_direction_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:46:05.376445+00:00
-- url     : https://prove2.me/submissions/22066982-7861-4004-a860-f91bdfdd6c1f

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CanonicalPoweredDecoder
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_Section5DecoderLayout_canonical_powered_decoder
import Theorems.Thm_section5_dyadic_entry_bound
import Theorems.Thm_section5_exact_integer_matrix_power_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

namespace Section5DecoderLayout



theorem matrix_components_disjoint {N K b f : ℕ} (s : Fin (K+1))
    (i j : Fin (2*(N+1)*(N+1))) (hij : i ≠ j) :
    ∀ e g, matrix (f:=f) s i e ≠ matrix (b:=b) s j g := by
  intro e g h
  have hh := (code N K b f).injective h
  exact hij (Wire.matrix.inj hh).2.1

theorem matrix_stages_disjoint {N K b f : ℕ} (s v : Fin (K+1)) (hsv : s ≠ v) :
    ∀ i j e g, matrix (N:=N) (f:=f) s i e ≠ matrix (b:=b) v j g := by
  intro i j e g h
  have hh := (code N K b f).injective h
  exact hsv (Wire.matrix.inj hh).1

theorem power_preserves_clean {N K b f : ℕ} (z z' : Qubits (width N K b f))
    (hz : Clean z)
    (hoff : ∀ j, (∀ s : Fin K, ∀ i, j ∉ Set.range (matrix s.succ i)) → z' j=z j) :
    Clean z' := by
  intro w hw
  refine (hoff _ ?_).trans (hz w hw)
  intro s i ⟨e,he⟩
  have hh := (code N K b f).injective he
  rw [← hh] at hw
  cases hw



end Section5DecoderLayout

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/































































theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Statistical operator error implies the real, sign-ambiguous direction guarantee
used by Theorem 5.6. This is the reconstruction guarantee; no efficient measurement
or classical eigenvector algorithm is assumed to have been constructed here. -/

theorem section5_complexify_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖section5_complexify w‖=‖w‖ := by
  have hs : ‖section5_complexify w‖^2=‖w‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,section5_complexify,WithLp.ofLp_toLp,
      Complex.norm_real]
  nlinarith [norm_nonneg w,norm_nonneg (section5_complexify w)]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N K b f q c : ℕ)
    (hn : N+1 ≤ 2^c) (hwidth : (K+1)*(q+1+c+1) < b)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1) :
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      circ.size ≤ (88*(N+1)^3*(b+1)^3)*K+Section5DecoderLayout.decoderGateBound N b f ∧
      ∀ z : Qubits (Section5DecoderLayout.width N K b f), Section5DecoderLayout.Clean z →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (Section5DecoderLayout.matrix s i e)=false) →
        let M := section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) 0) z
        IsSelfAdjoint (M.dyadicOperator q) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits (Section5DecoderLayout.width N K b f), act circ.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => Section5DecoderLayout.output N K b f i e.rev,
              fun _ _ h => Fin.rev_injective ((Section5DecoderLayout.output N K b f i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by
  have hpa : ∀ s i e j, Section5DecoderLayout.matrix (f:=f) s i e ≠ Section5DecoderLayout.powerAnc N K b f j := by
    intro s i e j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hpt : ∀ s i e, Section5DecoderLayout.matrix (f:=f) s i e ≠ Section5DecoderLayout.code N K b f Wire.powerScratch := by
    intro s i e h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hta : ∀ j, Section5DecoderLayout.code N K b f Wire.powerScratch ≠ Section5DecoderLayout.powerAnc N K b f j := by
    intro j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  obtain ⟨cp,hp,hpa'⟩ := section5_exact_integer_matrix_power_circuit (a:=q+1) hn hwidth Section5DecoderLayout.matrix
    (Section5DecoderLayout.powerAnc N K b f) (Section5DecoderLayout.code N K b f Wire.powerScratch) Section5DecoderLayout.matrix_components_disjoint
    Section5DecoderLayout.matrix_stages_disjoint hpa hpt hta
  obtain ⟨cd,hd,hda⟩ := Section5DecoderLayout.canonical_powered_decoder N K b f q hf hfit
  refine ⟨cp++cd,?_,?_⟩
  · simpa only [Circuit.size,List.length_append,Section5DecoderLayout.decoderGateBound] using add_le_add hp hd
  · intro z hz hzfuture
    dsimp only
    intro hM ε hε hε' hiter hbits w hw herror
    have hbound := section5_dyadic_entry_bound (section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) 0) z) q
      (section5_complexify w) (by rwa [section5_complexify_norm])
      (herror.trans (by linarith : ε/2000 ≤ 1))
    obtain ⟨z1,hz1,hpower,hzt,hza,hoff⟩ := hpa' z (hz _ rfl) (fun j => hz _ rfl) hzfuture hbound
    obtain ⟨z2,hz2,hout⟩ := hda z1 (Section5DecoderLayout.power_preserves_clean z z1 hz hoff)
      (section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) 0) z) hM hpower
      ε hε hε' hiter hbits w hw herror
    refine ⟨z2,?_,hout⟩
    rw [section5_boolean_circuit_append,hz1,hz2]
