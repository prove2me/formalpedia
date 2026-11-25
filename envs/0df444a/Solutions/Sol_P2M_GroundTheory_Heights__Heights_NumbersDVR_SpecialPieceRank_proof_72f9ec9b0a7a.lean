-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialPieceRank_proof_72f9ec9b0a7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:14.885846+00:00
-- url     : https://prove2.me/submissions/9519a757-e127-4f5a-b7b2-6ba5c3e24369

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialPieceRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpecialPieceRank
theorem _root_.solution (h1 : GradedPieceFree.Statement.{u}) : SpecialPieceRank.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m
  obtain ⟨hfree, hfin⟩ := h1 O ϖ hϖ K ι P htor m
  let ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O) :=
    mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))
  have hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f := fun f => rfl
  have hle : P ≤ (specialIdeal P).comap ρ := fun x hx => by
    rw [Ideal.mem_comap, hρ]
    exact Ideal.mem_map_of_mem _ hx
  let T := Ideal.quotientMapₐ (specialIdeal P) ρ hle
  have hT : ∀ f, T (Ideal.Quotient.mk P f) =
      Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) := fun f => rfl
  have hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩
  let b := Module.Free.chooseBasis O (gradedPieceR P m)
  let v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m :=
    fun i => ⟨T (b i), hTM _ (b i).2⟩
  have hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i) := fun i => rfl
  have hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P),
      IsLocalRing.residue O c • x = c • x := fun c x => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hli : LinearIndependent (IsLocalRing.ResidueField O) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun j => IsLocalRing.residue_surjective (g j)
    let y : gradedPieceR P m := ∑ j, c j • b j
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 y.2
    have hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P) := hfy
    have h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0 := by
      rw [← hT, hfy']
      have hg' := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'
      simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      rw [← hg']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j, hsmul]
    obtain ⟨p, hp, g0, hg0, hfp⟩ :=
      exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let z : gradedPieceR P m := ⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩
    have hyz : y = ϖ • z := by
      apply Subtype.ext
      rw [← hfy', hfp, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul,
        Submodule.coe_smul]
      show _ = ϖ • Ideal.Quotient.mk P g0
      rw [← map_mul, C_mul']
      exact map_smul (Ideal.Quotient.mkₐ O P) ϖ g0
    have hbli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbli
    have key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0 := by
      have e1 : ∑ j, (c j - ϖ * b.repr z j) • b j =
          ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (sub_smul (c j) (ϖ * b.repr z j) (b j)).trans
          (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))
      rw [e1, b.sum_repr]
      exact sub_eq_zero.2 hyz
    have hi := hbli _ key i
    rw [← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := exists_form_map_residue_eq hg
    let y : gradedPieceR P m := ⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢
    change _ = T (y : MRing ι O ⧸ P)
    rw [← hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hv, hsmul]
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]
end SpecialPieceRank
end GroundTheory.Heights₂.Heights.NumbersDVR
