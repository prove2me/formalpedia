-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.genericSection_of_axioms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:10.294574+00:00
-- url     : https://prove2.me/submissions/1482f3e4-cb22-4372-ad56-c004f1cb2a2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SectionSheafQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_fieldOfS


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
theorem _root_.solution (hd : d.AxH 𝒜) : d.S1 := by
  intro c
  have hS := (ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c)
    (hd.a1 c)).1
  have key : ∀ {M : Type} (j0 : Fin (d.N + 1)) (a : M) (f : Fin d.N → M),
      Fin.succAboveCases (α := fun _ => M) j0 a f j0 = a ∧
      ∀ k, Fin.succAboveCases (α := fun _ => M) j0 a f (j0.succAbove k) = f k :=
    fun j0 a f => ⟨by exact Fin.insertNth_apply_same (α := fun _ => _) j0 a f,
      fun k => by exact Fin.insertNth_apply_succAbove (α := fun _ => _) j0 a f k⟩
  let σ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.succAboveCases (α := fun _ => Fin (d.N + 1)) (d.jc c) 0 Fin.succ
  let ρ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.cases (motive := fun _ => Fin (d.N + 1)) (d.jc c) (d.jc c).succAbove
  have hρσ : Function.LeftInverse ρ σ := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [σ, ρ, (key _ _ _).1, Fin.cases_zero]
    · simp only [σ, ρ, (key _ _ _).2, Fin.cases_succ]
  let g : TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, σ p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (hρσ.injective hpq.2)
  have heq : ∀ p, sImg (d.jc c) (d.x c) p = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) (g p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).1, Fin.cases_zero]
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).2, Fin.cases_succ]
  have hfun : sImg (d.jc c) (d.x c) = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) ∘ g := funext heq
  have hI : AlgebraicIndependent K (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [hfun]
    exact hS.comp g hg
  exact hI
end ReciprocityTheory.ChartRestriction.G.T0.Data
