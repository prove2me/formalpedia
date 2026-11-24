-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ConservationOfNumberLE_proof_387d54420c16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:48.354806+00:00
-- url     : https://prove2.me/submissions/8588bc86-38e2-4eb6-9054-0fdd5de50329

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
private theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)
private theorem special_dim_add_one_le {O : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} {ι : K → Type}
    (P : Ideal (MRing ι O)) [P.IsPrime] (hnt : P.comap (C : O →+* MRing ι O) = ⊥) :
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) + 1 ≤
      ringKrullDim (MRing ι O ⧸ P) := by
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
end
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ConservationOfNumberLE
theorem _root_.solution (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u}) :
    ConservationOfNumberLE.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP hnt hdim a

  have hPprime : P.IsPrime := hP.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]

  have hsp : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    lt_of_add_one_le_natCast ((special_dim_add_one_le hϖ P hnt).trans hdim)
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom) hsp a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)
end ConservationOfNumberLE
end GroundTheory.Heights₂.Heights.NumbersDVR
