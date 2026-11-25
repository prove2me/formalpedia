-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension.basis_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:12.972773+00:00
-- url     : https://prove2.me/submissions/3af84db7-fa58-4257-9779-3fc24468b283

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LinearIndependentC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
theorem _root_.solution [FiniteDimensional L E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n L E) :
    letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
      (liftY (L := L) (E := E) (σ := σ)).toAlgebra;
    ∃ b' : Module.Basis n (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)),
      (∀ i, b' i = algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (b i))) ∧
      ∀ e : E, Algebra.leftMulMatrix b' (algebraMap (MvPolynomial σ E)
          (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e)) =
        (Algebra.leftMulMatrix b e).map (algebraMap L (FractionRing (MvPolynomial σ L))) := by

  try intro _
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := (liftY (L := L) (E := E) (σ := σ)).toAlgebra
  letI : Algebra (MvPolynomial σ L) (MvPolynomial σ E) := MvPolynomial.algebraMvPolynomial
  classical
  have hlift : ∀ q : MvPolynomial σ L, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.map (algebraMap L E) q) := by
    intro q
    show liftY (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) = _
    simp only [liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hsmul : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      q • P = MvPolynomial.map (algebraMap L E) q * P := fun q P => by
    rw [Algebra.smul_def]; rfl
  have himg : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (q • P) = algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P := by
    intro q P; rw [hsmul, map_mul, hlift]
  have hmem : ∀ P : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro P
    rw [PolynomialCoordinateBasis.eq_sum_crd b P, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [himg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (FractionRing (MvPolynomial σ L)) (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial σ L))
      Finset.univ g
    have hd' : ∀ j, ∃ a : MvPolynomial σ L, algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) a = (d : MvPolynomial σ L) • g j :=
      fun j => hd j (Finset.mem_univ j)
    choose a ha using hd'
    have h0 : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E)) = 0 := by
      rw [map_sum]
      simp only [himg, ha]
      have e1 : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) ((d : MvPolynomial σ L) • g j) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
          algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) d) * ∑ j, g j • algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      rw [e1]
      beta_reduce at hg
      rw [hg, mul_zero]
    have h1 : ∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E) = 0 :=
      IsFractionRing.injective _ (FractionRing (MvPolynomial σ E)) (by rw [h0, map_zero])
    have h2 := (Fintype.linearIndependent_iff.mp (PolynomialCoordinateBasis.linearIndependent_C (σ := σ) b)) a h1 i
    have h3 : (d : MvPolynomial σ L) • g i = 0 := by rw [← ha i, h2, map_zero]
    rw [Algebra.smul_def] at h3
    exact (mul_eq_zero.mp h3).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  have hmul : ∀ x ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), ∀ y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), x * y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x hx y hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    show algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b k)) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b l)) ∈ _
    rw [← map_mul]; exact hmem _
  have hone : (1 : FractionRing (MvPolynomial σ E)) ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by simpa using hmem 1
  have hfg : (Subalgebra.toSubmodule ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))).FG := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  have htop : ⊤ ≤ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x _
    obtain ⟨a, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ E) x
    have hint := IsIntegral.of_mem_of_fg _ hfg (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q) (hmem q)
    have hinv := Subalgebra.inv_mem_of_algebraic ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))
      (x := ⟨algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q, hmem q⟩) hint.isAlgebraic
    rw [div_eq_mul_inv]
    exact hmul _ (hmem a) _ hinv
  refine ⟨Module.Basis.mk hli htop, fun i => Module.Basis.mk_apply _ _ _, fun e => ?_⟩
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.mk_apply]
  have hx : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
      ∑ k, algebraMap L (FractionRing (MvPolynomial σ L)) (b.repr (e * b j) k) • (Module.Basis.mk hli htop) k := by
    rw [← map_mul, ← MvPolynomial.C_mul]
    conv_lhs => rw [← b.sum_repr (e * b j)]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Module.Basis.mk_apply, Algebra.smul_def (algebraMap L (FractionRing (MvPolynomial σ L)) _),
      IsScalarTower.algebraMap_apply L (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)), MvPolynomial.algebraMap_eq,
      ← himg, hsmul, MvPolynomial.map_C, ← MvPolynomial.C_mul, Algebra.smul_def]
  beta_reduce
  rw [hx, Module.Basis.repr_sum_self]
end ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
