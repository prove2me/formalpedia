-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace.trace_aeval_div_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:34.545833+00:00
-- url     : https://prove2.me/submissions/8165e090-36e5-4dfc-9e64-ccdd613fba2b

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace

set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace
open Polynomial
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace
theorem _root_.solution (p b : k[X])
    [hirr : Fact (Irreducible p)] (hp : p.Monic) (hb : b.degree < p.degree) :
    Algebra.trace k (AdjoinRoot p)
        (Polynomial.aeval (AdjoinRoot.root p) b /
          Polynomial.aeval (AdjoinRoot.root p) p.derivative) =
      b.coeff (p.natDegree - 1) := by
  classical
  letI : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let pb : PowerBasis k (AdjoinRoot p) := AdjoinRoot.powerBasis' hp
  have hdegree_pos : 0 < p.natDegree := hirr.out.natDegree_pos
  let last : Fin p.natDegree :=
    ⟨p.natDegree - 1, Nat.sub_lt hdegree_pos Nat.zero_lt_one⟩
  have hminpoly : minpoly k pb.gen = p := by
    change minpoly k (AdjoinRoot.root p) = p
    simpa only [AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic hp
  have hminpolyDiv_degree :
      (minpolyDiv k pb.gen).natDegree = p.natDegree - 1 := by
    rw [natDegree_minpolyDiv, hminpoly]
  have hminpolyDiv_coeff : (minpolyDiv k pb.gen).coeff last = 1 := by
    change (minpolyDiv k pb.gen).coeff (p.natDegree - 1) = 1
    rw [← hminpolyDiv_degree]
    exact (minpolyDiv_monic (Algebra.IsIntegral.isIntegral pb.gen)).coeff_natDegree
  have hdual :
      pb.basis.traceDual last =
        (Polynomial.aeval pb.gen p.derivative)⁻¹ := by
    rw [Module.Basis.traceDual_powerBasis_eq pb last, hminpoly,
      hminpolyDiv_coeff]
    simp
  have htrace :
      Algebra.trace k (AdjoinRoot p)
          (Polynomial.aeval pb.gen b * pb.basis.traceDual last) =
        pb.basis.repr (Polynomial.aeval pb.gen b) last := by
    have h := Module.Basis.traceDual_repr_apply
      (b := pb.basis.traceDual) (x := Polynomial.aeval pb.gen b) last
    rw [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply] at h
    exact h.symm
  have hrepr :
      pb.basis.repr (Polynomial.aeval pb.gen b) last =
        b.coeff (p.natDegree - 1) := by
    rw [show pb.basis = AdjoinRoot.powerBasisAux' hp by rfl,
      show pb.gen = AdjoinRoot.root p by rfl,
      AdjoinRoot.aeval_eq]
    change (AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk p b)).coeff last = _
    rw [AdjoinRoot.modByMonicHom_mk,
      (modByMonic_eq_self_iff hp).mpr hb]
  calc
    Algebra.trace k (AdjoinRoot p)
        (Polynomial.aeval (AdjoinRoot.root p) b /
          Polynomial.aeval (AdjoinRoot.root p) p.derivative) =
        Algebra.trace k (AdjoinRoot p)
          (Polynomial.aeval pb.gen b * pb.basis.traceDual last) := by
            rw [hdual]
            rfl
    _ = pb.basis.repr (Polynomial.aeval pb.gen b) last := htrace
    _ = b.coeff (p.natDegree - 1) := hrepr
end QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace
