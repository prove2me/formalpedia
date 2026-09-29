-- Prove2me | solution 1 for PDivisibleGroup.finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ade966ab-c373-5a39-9c1d-2a52360725b2

import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Theorems.Thm_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
set_option Elab.async false

namespace Ws47
namespace RANK

variable (p : ℕ) [Fact p.Prime]

open scoped Pointwise

theorem natCard_padicInt_quotient_span_pow (v : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {((p : ℤ_[p]) ^ v)}) = p ^ v := by
  have hker : RingHom.ker (PadicInt.toZModPow v : ℤ_[p] →+* ZMod (p ^ v)) = Ideal.span {((p : ℤ_[p]) ^ v)} :=
    PadicInt.ker_toZModPow v
  have e : ℤ_[p] ⧸ Ideal.span {((p : ℤ_[p]) ^ v)} ≃+* ZMod (p ^ v) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow v)))
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

theorem mem_pow_smul_top_iff {ι : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℤ_[p] V]
    (b : Module.Basis ι ℤ_[p] V) (v : ℕ) (x : V) :
    x ∈ ((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V) ↔ ∀ i, ((p : ℤ_[p]) ^ v) ∣ b.repr x i := by
  constructor
  · rintro hx i
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact ⟨b.repr y i, by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]⟩
  · intro h
    choose c hc using h
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨∑ i, c i • b i, Submodule.mem_top, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← hc i]

theorem natCard_quotient_pow_smul_top {V : Type} [AddCommGroup V] [Module ℤ_[p] V] [Module.Free ℤ_[p] V]
    [Module.Finite ℤ_[p] V] (v : ℕ) :
    Nat.card (V ⧸ ((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V)) = p ^ (v * Module.finrank ℤ_[p] V) := by
  classical
  let n := Module.finrank ℤ_[p] V
  let b : Module.Basis (Fin n) ℤ_[p] V := Module.finBasis ℤ_[p] V

  let e : V ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := b.equivFun
  let I : Ideal ℤ_[p] := Ideal.span {((p : ℤ_[p]) ^ v)}

  have himg : (((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V)).map (e : V →ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
      = Submodule.pi Set.univ (fun _ : Fin n => (I.restrictScalars ℤ_[p] : Submodule ℤ_[p] ℤ_[p])) := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.restrictScalars_mem]
    have hI : ∀ z : ℤ_[p], z ∈ I ↔ ((p : ℤ_[p]) ^ v) ∣ z := fun z => Ideal.mem_span_singleton
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      rw [hI]
      have := (mem_pow_smul_top_iff p b v x).1 hx i
      rwa [show (e : V →ₗ[ℤ_[p]] (Fin n → ℤ_[p])) x i = b.repr x i from congrFun (Module.Basis.equivFun_apply b x) i]
    · intro hy
      refine ⟨e.symm y, (mem_pow_smul_top_iff p b v _).2 (fun i => ?_), e.apply_symm_apply y⟩
      have : b.repr (e.symm y) i = y i := by
        have h1 := congrFun (Module.Basis.equivFun_apply b (e.symm y)) i
        rw [show b.equivFun (e.symm y) = y from e.apply_symm_apply y] at h1
        exact h1.symm
      rw [this]; exact (hI _).1 (hy i)
  have e1 : (V ⧸ ((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V)) ≃ₗ[ℤ_[p]]
      ((Fin n → ℤ_[p]) ⧸ Submodule.pi Set.univ (fun _ : Fin n => (I.restrictScalars ℤ_[p] : Submodule ℤ_[p] ℤ_[p]))) :=
    Submodule.Quotient.equiv _ _ e himg
  have e2 := Submodule.quotientPi (fun _ : Fin n => (I.restrictScalars ℤ_[p] : Submodule ℤ_[p] ℤ_[p]))
  rw [Nat.card_congr (e1.trans e2).toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : Nat.card (ℤ_[p] ⧸ (I.restrictScalars ℤ_[p] : Submodule ℤ_[p] ℤ_[p])) = p ^ v :=
    natCard_padicInt_quotient_span_pow p v
  rw [this, ← pow_mul]

theorem index_pow_smul_top {V : Type} [AddCommGroup V] [Module ℤ_[p] V] [Module.Free ℤ_[p] V]
    [Module.Finite ℤ_[p] V] (v : ℕ) :
    (((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V)).toAddSubgroup.index = p ^ (v * Module.finrank ℤ_[p] V) :=
  natCard_quotient_pow_smul_top p v

theorem natCard_range_of_ker_eq {V : Type} [AddCommGroup V] [Module ℤ_[p] V] [Module.Free ℤ_[p] V] [Module.Finite ℤ_[p] V]
    {W : Type} [AddCommGroup W] (f : V →+ W) (v : ℕ)
    (hker : f.ker = (((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] V)).toAddSubgroup) :
    Nat.card f.range = p ^ (v * Module.finrank ℤ_[p] V) := by
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).symm.toEquiv, ← AddSubgroup.index, hker]
  exact index_pow_smul_top p v

theorem algHom_comp_injective_of_surjective {R A B C : Type} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] (π : A →ₐ[R] B) (hπ : Function.Surjective π) {f g : B →ₐ[R] C}
    (h : f.comp π = g.comp π) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact DFunLike.congr_fun h a

end Ws47.RANK

universe u v w

set_option maxHeartbeats 6400000 in
open scoped Pointwise in
open Ws47.RANK in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :
    (∀ v, Module.finrank (PadicAlgCl.ringOfIntegers p K) (B v) = p ^ (v * Module.finrank ℤ_[p] ↥M)) ∧
    (∀ v, Module.finrank (PadicAlgCl.ringOfIntegers p K) ↥(HopfAlgebra.hopfKer (t v)) = p ^ Module.finrank ℤ_[p] ↥M) := by
  classical

  obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI : IsDiscreteValuationRing ↥(PadicAlgCl.ringOfIntegers p K) := hdvr
  haveI : CharZero ↥(PadicAlgCl.ringOfIntegers p K) := by
    refine charZero_of_injective_algebraMap (R := ℤ_[p]) (A := ↥(PadicAlgCl.ringOfIntegers p K)) ?_
    have hcomp : Function.Injective ((algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).comp
        (algebraMap ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K))) := by
      rw [← IsScalarTower.algebraMap_eq ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)]
      exact PadicAlgCl.ringOfIntegers.algebraMap_injective_padicInt p
    rw [RingHom.coe_comp] at hcomp
    exact Function.Injective.of_comp hcomp

  have hlev : ∀ v : ℕ, Finite (G.Point (PadicAlgCl p) v) ∧ Nat.card (G.Point (PadicAlgCl p) v) = p ^ (v * h) :=
    fun v => PDivisibleGroup.finite_point_and_natCard_point_eq_pow p G (PadicAlgCl p) v
  obtain ⟨-, hker, hfree, hrank⟩ :=
    PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq p G (PadicAlgCl p) hlev
  haveI : Module.Free ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))) := hfree

  haveI : Module.Finite ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))) := by
    by_cases hh : h = 0
    ·
      subst hh
      haveI : Subsingleton (TateModule p (G.Points (PadicAlgCl p))) := by
        refine ⟨fun x y => Subtype.ext (funext fun v => ?_)⟩
        have hsub : ∀ v, Subsingleton (G.Point (PadicAlgCl p) v) := fun v => by
          haveI := (hlev v).1
          have hc := (hlev v).2
          rw [mul_zero, pow_zero] at hc
          exact (Nat.card_eq_one_iff_unique.1 hc).1

        have hx := (PDivisibleGroup.nsmul_eq_zero_iff_exists_pointsMkAdd_eq G (PadicAlgCl p) v ((x : ℕ → G.Points (PadicAlgCl p)) v)).1
          (by rw [← natCast_zsmul]; exact_mod_cast TateModule.torsion x v)
        have hy := (PDivisibleGroup.nsmul_eq_zero_iff_exists_pointsMkAdd_eq G (PadicAlgCl p) v ((y : ℕ → G.Points (PadicAlgCl p)) v)).1
          (by rw [← natCast_zsmul]; exact_mod_cast TateModule.torsion y v)
        obtain ⟨gx, hgx⟩ := hx
        obtain ⟨gy, hgy⟩ := hy
        rw [← hgx, ← hgy, (hsub v).elim gx gy]
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [hrank]; exact Nat.pos_of_ne_zero hh)

  haveI : IsNoetherian ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))) := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] _
  haveI : Module.Finite ℤ_[p] ↥M := Module.Finite.of_injective M.subtype Subtype.val_injective
  haveI : NoZeroSMulDivisors ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))) := ⟨fun {c x} hcx => by
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl hc
    · right
      let bT := Module.Free.chooseBasis ℤ_[p] (TateModule p (G.Points (PadicAlgCl p)))
      have h1 := congrArg bT.repr hcx
      rw [map_smul, map_zero] at h1
      exact bT.repr.injective (by rw [map_zero]; exact (smul_eq_zero.1 h1).resolve_left hc)⟩
  haveI : NoZeroSMulDivisors ℤ_[p] ↥M := ⟨fun {c x} hcx => by
    have h1 : c • (x : TateModule p (G.Points (PadicAlgCl p))) = 0 := by
      rw [← Submodule.coe_smul, hcx, Submodule.coe_zero]
    exact (smul_eq_zero.1 h1).imp id (fun h => Subtype.ext h)⟩
  haveI : Module.Free ℤ_[p] ↥M := Module.free_of_finite_type_torsion_free'

  have h1 : ∀ v, Module.finrank ↥(PadicAlgCl.ringOfIntegers p K) (B v) = p ^ (v * Module.finrank ℤ_[p] ↥M) := by
    intro v

    let fM : ↥M →+ G.Points (PadicAlgCl p) :=
      (TateModule.proj p (G.Points (PadicAlgCl p)) v).comp M.subtype.toAddMonoidHom
    have hfM : ∀ x : ↥M, fM x = ((x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) v := fun _ => rfl

    have e1 : (B v →ₐ[↥(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) ≃ {g : G.Point (PadicAlgCl p) v //
        ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) v} := by
      refine (Equiv.ofBijective (fun f => (⟨PDivisibleGroup.Point.ofAlgHom (f.comp (π v : G.level v →ₐ[↥(PadicAlgCl.ringOfIntegers p K)] B v)), f, rfl⟩ :
          {g : G.Point (PadicAlgCl p) v // ∃ g' : B v →ₐ[↥(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[↥(PadicAlgCl.ringOfIntegers p K)] B v) = PDivisibleGroup.Point.toAlgHom g})) ⟨?_, ?_⟩).trans
        (Equiv.subtypeEquivRight (hpts v))
      · intro f f' hff'
        have := congrArg (fun g => PDivisibleGroup.Point.toAlgHom g.1) hff'
        exact algHom_comp_injective_of_surjective _ (hπ v) this
      · rintro ⟨g, g', hg'⟩
        exact ⟨g', Subtype.ext (by show PDivisibleGroup.Point.ofAlgHom _ = g; rw [hg']; rfl)⟩

    have e2 : {g : G.Point (PadicAlgCl p) v //
        ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) v} ≃ fM.range := by
      refine Equiv.ofBijective (fun g => ⟨G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g.1), ?_⟩) ⟨?_, ?_⟩
      · obtain ⟨x, hx, hgx⟩ := g.2
        exact ⟨⟨x, hx⟩, hgx.symm⟩
      · intro g g' hgg'
        have := congrArg Subtype.val hgg'
        exact Subtype.ext (Additive.ofMul.injective (G.pointsMkAdd_injective v this))
      · rintro ⟨y, x, rfl⟩
        have htor : (p ^ v) • fM x = 0 := by
          rw [hfM, ← natCast_zsmul]
          exact_mod_cast TateModule.torsion (x : TateModule p (G.Points (PadicAlgCl p))) v
        obtain ⟨g, hg⟩ := (PDivisibleGroup.nsmul_eq_zero_iff_exists_pointsMkAdd_eq G (PadicAlgCl p) v _).1 htor
        exact ⟨⟨g, x, x.2, by rw [hg, hfM]⟩, Subtype.ext hg⟩

    have hkerM : fM.ker = (((p : ℤ_[p]) ^ v) • (⊤ : Submodule ℤ_[p] ↥M)).toAddSubgroup := by
      ext x
      rw [AddMonoidHom.mem_ker, hfM, Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists]
      constructor
      · intro hx0
        obtain ⟨z, hz⟩ := (hker v x).1 hx0
        have hpv : ((p : ℤ_[p]) ^ v) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
        have hzM : z ∈ M := hMsat _ z hpv (by rw [← hz]; exact x.2)
        exact ⟨⟨z, hzM⟩, Submodule.mem_top, Subtype.ext (by rw [Submodule.coe_smul]; exact hz.symm)⟩
      · rintro ⟨m, -, rfl⟩
        exact (hker v _).2 ⟨m, by rw [Submodule.coe_smul]⟩

    have hc : Nat.card (B v →ₐ[↥(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p) = Module.finrank ↥(PadicAlgCl.ringOfIntegers p K) (B v) :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ↥(PadicAlgCl.ringOfIntegers p K) (B v) (PadicAlgCl p)
    have hcard := natCard_range_of_ker_eq p fM v hkerM
    rw [← hc, Nat.card_congr (e1.trans e2), hcard]
  refine ⟨h1, fun v => ?_⟩

  have hmul := HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective
    (R := ↥(PadicAlgCl.ringOfIntegers p K)) (A := B (v + 1)) (B := B v) (t v) (ht v)
  have e1 := h1 v
  have e2 := h1 (v + 1)
  rw [Nat.succ_mul, pow_add] at e2
  rw [e1, e2] at hmul
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) (by rw [hmul, mul_comm])

end S_PDivisibleGroup_finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_finrank_eq_pow_mul_finrank_and_finrank_hopfKer_eq_of_hopf_quotient_system_of_ringOfIntegers (solution)
