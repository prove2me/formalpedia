-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.height_ker_scaledSubstitution_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:29:21.585258+00:00
-- url     : https://prove2.me/submissions/d55276db-9aee-45c0-b49b-b4043175a386

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightKerScaledSubstitutionLeOne
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_optionEquivLeft_rename_some__c92b016ed5b6
import Theorems.Thm_ReciprocityTheory_CA_height_le_one_of_comap_C_eq_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_scaledSubstitution_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algebraicIndependent_scaledForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scalarRatio_self
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_exists_dual_derivations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha
end ReciprocityTheory.ChartRestriction.G.T0.Data
