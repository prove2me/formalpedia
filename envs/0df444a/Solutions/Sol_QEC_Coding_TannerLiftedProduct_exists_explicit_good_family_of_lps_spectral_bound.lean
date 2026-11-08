-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_explicit_good_family_of_lps_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:58:23.511815+00:00
-- url     : https://prove2.me/submissions/66965e46-0302-4cb1-bc8b-f5fd305c82e0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Definitions.Def_QEC_Results_QLDPC_ConditionalLiftedProductFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_decodeTyped_output
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_mem_originalFamily_carrier_iff_decodedOutput
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_decodeTyped_output
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22LPSFamily_of_ramanujanComplexOperatorBound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_608e2928fd_22
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22ConditionalQubitDecidableEq
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate) (hRate : targetRate < 1)
    (hLPS : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ),
      SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 B))
        (2 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F)
      (e : Fin (Fintype.card F) ≃ F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one a.prime a.oneModFour
      let family := lpsSemanticFamily a.prime a.oneModFour hCount h h'
      let r := pk22RowCoefficient (Nat.card F) t * a.blocks
      let tables := encodedFieldTables e
      let g := LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour
      let hc := h.map e.symm
      let hc' := h'.map e.symm
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily family ∧
      QEC.QLDPC.HasEventualRateAtLeast family targetRate ∧
      (∀ B : ℕ,
        LPSSparseEmitterFamily.physicalSize
          (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B) (a.p + 1) r r =
            family.blockLength B) ∧
      (∀ B : ℕ, Nonempty (TM2OutputsInTime
        (LPSSparseEmitterFamily.sourceMachine a.prime a.oneModFour tables hc hc').toFinTM2
        (unary B)
        (some (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc'))
        ((LPSSparseEmitterFamily.sourceTime a.prime a.oneModFour tables hc hc').eval
          (family.blockLength B)))) ∧
      (∀ B : ℕ,
        LPSSparseEmitterCodec.decodeTyped
          (LPSSparseEmitterFamily.PhysicalCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q (a.p + 1) r r)
          (Fintype.card F)
          (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') =
        some (lpsEncodedCheckOutput tables
          (fun j => lpsEffectiveQuaternionFamilyIndex a.prime a.oneModFour B (g j))
          hc hc')) ∧
      (∀ (B : ℕ)
        (ψ : Semantics.Qudit.QuditRegister
          (fun _ : FamilyQubitIndex
            (W := Fin (a.p + 1)) (R := PK22Check (Nat.card F) t a)
            (R' := PK22Check (Nat.card F) t a)
            (G := LPSVertexGroup a.prime a.oneModFour) B => Fintype.card F)),
        ψ ∈ (family.presentation B).code.carrier ↔
          ∀ i : Fin (LPSSparseEmitterFamily.CheckCount
            (lpsEffectiveResiduePrimeAt a.prime a.oneModFour B).q
            (a.p + 1) r r (Fintype.card F)),
          LPSSparseEmitterFamily.decodedOperator e tables i
            (LPSSparseEmitterFamily.sourceOutput a.prime a.oneModFour B tables hc hc') ψ = ψ) := by
  classical
  obtain ⟨t, a, h, h', hGood, hRequestedRate⟩ :=
    exists_pk22LPSFamily_of_ramanujanComplexOperatorBound
      F targetRate hRatePositive hRate hLPS
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  refine ⟨t, a, h, h', e, hGood, hRequestedRate, ?_, ?_, ?_, ?_⟩
  · intro B
    rfl
  · intro B
    exact ⟨Machine.outputsInTime _ _ _ _
      (LPSSparseEmitterFamily.sourceExec a.prime a.oneModFour B
        (encodedFieldTables e) (h.map e.symm) (h'.map e.symm))⟩
  · intro B
    exact LPSSparseEmitterFamily.decodeTyped_output
      a.prime a.oneModFour B
      (LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour)
      (encodedFieldTables e) (h.map e.symm) (h'.map e.symm)
  · intro B ψ
    exact LPSSparseEmitterFamily.mem_originalFamily_carrier_iff_decodedOutput
      e a.prime a.oneModFour B
      (LPSSparseEmitterFamily.sourceDirections a.prime a.oneModFour) h h' ψ
end QEC.Coding.TannerLiftedProduct
