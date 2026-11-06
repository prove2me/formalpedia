-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:17.489406+00:00
-- url     : https://prove2.me/submissions/1747ca5b-8b48-4521-b066-c1dbe260704a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_AnnihilatedTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
private theorem primaryTorsionLayer_zero_eq_bot (p : Ideal R) :
    primaryTorsionLayer p M 0 = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [primaryTorsionLayer, pow_zero,
      Submodule.mem_torsionBySet_iff] at hx
    have hx_one := hx (⟨1, by simp⟩ : (1 : Ideal R))
    change x = 0
    simpa only [one_smul] using hx_one
  · exact bot_le
private theorem primaryTorsionLayer_eq_top_of_annihilated
    (p : Ideal R) (hM : Module.IsTorsionBySet R M p)
    (i : ℕ) (hi : 0 < i) :
    primaryTorsionLayer p M i = ⊤ := by
  apply eq_top_iff.mpr
  intro x _hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  exact @hM x ⟨a, Ideal.pow_le_self (Nat.ne_of_gt hi) a.property⟩
private theorem primaryTorsionGrade_subsingleton_of_annihilated
    (p : Ideal R) (hM : Module.IsTorsionBySet R M p)
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (primaryTorsionGrade p M i) := by
  rw [Submodule.Quotient.subsingleton_iff]
  apply eq_top_iff.mpr
  intro x _hx
  change (x : M) ∈ primaryTorsionLayer p M i
  rw [primaryTorsionLayer_eq_top_of_annihilated p hM i hi]
  exact Submodule.mem_top
private theorem primaryTorsionGradeTrace_eq_zero_of_annihilated
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    (hM : Module.IsTorsionBySet R M p)
    (f : M →ₗ[R] M) (i : ℕ) (hi : 0 < i) :
    primaryTorsionGradeTrace p f i = 0 := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Subsingleton (primaryTorsionGrade p M i) :=
    primaryTorsionGrade_subsingleton_of_annihilated p hM i hi
  rw [primaryTorsionGradeTrace]
  have hend : primaryTorsionGradeEndomorphism p f i = 0 :=
    Subsingleton.elim _ _
  rw [hend, map_zero]
private theorem primaryTorsionGradeTrace_zero_eq_trace_of_annihilated
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    (hM : Module.IsTorsionBySet R M p)
    [Module (R ⧸ p) M] [IsScalarTower R (R ⧸ p) M]
    (f : M →ₗ[R ⧸ p] M) :
    primaryTorsionGradeTrace p (f.restrictScalars R) 0 =
      LinearMap.trace (R ⧸ p) M f := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Module.Finite (R ⧸ p) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ p) M
  let hgrade := primaryTorsionGrade_annihilated (M := M) p 0
  letI : Module (R ⧸ p) (primaryTorsionGrade p M 0) := hgrade.module
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M 0) :=
    primaryTorsionGradeFinite (M := M) p 0
  have hzero : primaryTorsionLayer p M 0 = ⊥ :=
    primaryTorsionLayer_zero_eq_bot p
  have hone : primaryTorsionLayer p M 1 = ⊤ :=
    primaryTorsionLayer_eq_top_of_annihilated p hM 1 Nat.zero_lt_one
  have hprevious :
      (primaryTorsionLayer p M 0).comap
          (primaryTorsionLayer p M 1).subtype = ⊥ := by
    rw [hzero, Submodule.comap_bot, Submodule.ker_subtype]
  let eR : primaryTorsionGrade p M 0 ≃ₗ[R] M := by
    change
      (primaryTorsionLayer p M 1 ⧸
          (primaryTorsionLayer p M 0).comap
            (primaryTorsionLayer p M 1).subtype) ≃ₗ[R] M
    exact
      ((primaryTorsionLayer p M 0).comap
          (primaryTorsionLayer p M 1).subtype).quotEquivOfEqBot hprevious |>.trans
        ((LinearEquiv.ofEq _ _ hone).trans Submodule.topEquiv)
  let e : primaryTorsionGrade p M 0 ≃ₗ[R ⧸ p] M :=
    { toEquiv := eR.toEquiv
      map_add' := eR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change eR (Ideal.Quotient.mk p r • x) =
              (algebraMap R (R ⧸ p) r) • eR x
            rw [Module.IsTorsionBySet.mk_smul hgrade, eR.map_smul,
              IsScalarTower.algebraMap_smul] }
  let g := primaryTorsionGradeEndomorphism p (f.restrictScalars R) 0
  have hconj : e.conj g = f := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        rw [primaryTorsionGradeEndomorphism_mk]
        rfl
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M 0) g =
    LinearMap.trace (R ⧸ p) M f
  calc
    _ = LinearMap.trace (R ⧸ p) M (e.conj g) :=
      (LinearMap.trace_conj' g e).symm
    _ = _ := congrArg (LinearMap.trace (R ⧸ p) M) hconj
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    (hM : Module.IsTorsionBySet R M p)
    [Module (R ⧸ p) M] [IsScalarTower R (R ⧸ p) M]
    (f : M →ₗ[R ⧸ p] M) (n : ℕ) (hn : 0 < n) :
    primaryTorsionTrace p (f.restrictScalars R) n =
      LinearMap.trace (R ⧸ p) M f := by
  rw [primaryTorsionTrace]
  calc
    (∑ i ∈ Finset.range n,
        primaryTorsionGradeTrace p (f.restrictScalars R) i) =
        primaryTorsionGradeTrace p (f.restrictScalars R) 0 := by
      apply Finset.sum_eq_single 0
      · intro i hi hne
        exact primaryTorsionGradeTrace_eq_zero_of_annihilated
          p hM (f.restrictScalars R) i (Nat.pos_of_ne_zero hne)
      · intro hzero
        exact (hzero (Finset.mem_range.mpr hn)).elim
    _ = _ := primaryTorsionGradeTrace_zero_eq_trace_of_annihilated p hM f
end QEC.Coding.AlgebraicGeometry
