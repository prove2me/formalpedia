-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.colengthCotangentBound_of_claim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:30:37.279412+00:00
-- url     : https://prove2.me/submissions/e4344ba6-7b1c-44a5-9160-9a1a9aa600e2

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_le_of_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) (hcl : ColengthCotangentValuation p C v R)
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (hN : ∀ x : N, p • x = 0)
    (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal)
    (hlen : HasColen R v AA.carrier lenN) (hom : HasLen v R (OmAA AA.carrier) lenOm) :
    lenN ^ 2 ≤ lenOm ^ Fintype.card N := by
  obtain ⟨n, g, δ, hg, hgen, htri, hcol⟩ := hcl N hN AA
  let q := ((sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype).mkQ
  have key : ∀ x z : augIdeal AA.carrier,
      ((x : N → C) - z) ∈ sqIdeal (augIdeal AA.carrier) → q x = q z := by
    intro x z h
    exact (Submodule.Quotient.eq _).mpr (by simpa [Submodule.mem_comap] using h)
  let y : Fin n → OmAA AA.carrier := fun i => q ⟨g i, hg i⟩
  have hy : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨r, hr⟩ := hgen f hf
    have e : q ⟨f, hf⟩ = ∑ j, r j • y j := by
      simp only [y, ← map_smul, ← map_sum]
      apply key
      simpa using hr
    show q ⟨f, hf⟩ ∈ _
    rw [e]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j := by
    intro i
    obtain ⟨a, ha⟩ := htri i
    refine ⟨a, ?_⟩
    simp only [y, ← map_smul, ← map_sum]
    apply key
    have e2 : (((∑ j, (if j < i then a j else 0) • (⟨g j, hg j⟩ : augIdeal AA.carrier) :
        augIdeal AA.carrier)) : N → C) = ∑ j, (if j < i then a j else 0) • g j := by
      rw [Submodule.coe_sum]
      rfl
    rw [e2]
    exact ha
  have hle := prod_le_of_gen hv hom y hy δ hrel
  rw [hcol lenN hlen]
  first
    | exact pow_le_pow_left₀ zero_le hle _
    | exact pow_le_pow_left zero_le hle _
    | gcongr
end ReciprocityTheory.PGsh.Up
