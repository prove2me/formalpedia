-- Prove2me | solution 1 for WeierstrassCurve.mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2ac8f4f9-03e9-55d6-bf29-1547cc46f091

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_Module_End_mem_ideal_of_forall_apply_eq_zero_zmod
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion
p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map mk reduction toAffine Affine.Point Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero comp_mem_rationalHomSet add_mem_rationalHomSet"
p2m_open "WeierstrassCurve"

namespace KernelIdealFiniteLevel

section HomSet

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented K W W (-(AddMonoidHom.id _)) := by
  refine ⟨Polynomial.C Polynomial.X, 1,
    -Polynomial.X - Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC K (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC K (Polynomial.C Polynomial.X : F[X][Y]) x y = x := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC K (-Polynomial.X - Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) :
      F[X][Y]) x y = (W.baseChange K).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

variable {K}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) : -α ∈ rationalHomSet K W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet K W₁ W₂ W₂ hα
    (Or.inr (isRationallyRepresented_neg_id K W₂))
  have e : (-(AddMonoidHom.id _)).comp α = -α := AddMonoidHom.ext fun P => rfl
  rwa [e] at h

variable [IsAlgClosed K]

variable (K) in

def homSubring (W : WeierstrassCurve F) [W.IsElliptic] :
    Subring (AddMonoid.End (W.baseChange K).toAffine.Point) where
  carrier := rationalHomSet K W W
  mul_mem' ha hb := WeierstrassCurve.comp_mem_rationalHomSet K W W W hb ha
  one_mem' := id_mem_rationalHomSet K W
  add_mem' ha hb := WeierstrassCurve.add_mem_rationalHomSet K W W ha hb
  zero_mem' := zero_mem_rationalHomSet K W W
  neg_mem' hα := neg_mem_rationalHomSet hα

theorem mem_rationalHomSet_of_mem_rationalEndSubring (W : WeierstrassCurve F) [W.IsElliptic]
    {α : AddMonoid.End (W.baseChange K).toAffine.Point} (hα : α ∈ rationalEndSubring K W) :
    (α : (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point) ∈ rationalHomSet K W W := by
  have : rationalEndSubring K W ≤ homSubring K W := Subring.closure_le.mpr (fun x hx => hx)
  exact this hα

end HomSet

section Torsion

variable {κ : Type*} [Field κ] [DecidableEq κ] (X₀ : WeierstrassCurve κ)

abbrev Pt : Type _ := (X₀.baseChange κ).toAffine.Point

def Tor (n : ℕ) : Type _ := ↥(Submodule.torsionBy ℤ (Pt X₀) (n : ℤ))

scoped instance (n : ℕ) : AddCommGroup (Tor X₀ n) := inferInstanceAs (AddCommGroup ↥(Submodule.torsionBy ℤ (Pt X₀) (n : ℤ)))

def torEquiv (n : ℕ) : Tor X₀ n ≃+ ↥(Submodule.torsionBy ℤ (Pt X₀) (n : ℤ)) := AddEquiv.refl _

theorem nsmul_eq_zero (n : ℕ) (x : Tor X₀ n) : n • x = 0 := by
  apply (torEquiv X₀ n).injective
  rw [map_nsmul, map_zero]
  apply Subtype.ext
  have hx := ((torEquiv X₀ n) x).2
  rw [Submodule.mem_torsionBy_iff] at hx
  change (n • ((torEquiv X₀ n x : ↥(Submodule.torsionBy ℤ (Pt X₀) (n : ℤ))) : Pt X₀)) = 0
  rw [← natCast_zsmul]
  exact hx

scoped instance (n : ℕ) [NeZero n] : Module (ZMod n) (Tor X₀ n) := AddCommGroup.zmodModule (nsmul_eq_zero X₀ n)

def Tor.val {n : ℕ} (x : Tor X₀ n) : Pt X₀ := ((torEquiv X₀ n) x : Pt X₀)

theorem Tor.ext {n : ℕ} {x y : Tor X₀ n} (h : Tor.val X₀ x = Tor.val X₀ y) : x = y :=
  (torEquiv X₀ n).injective (Subtype.ext h)

theorem Tor.val_add {n : ℕ} (x y : Tor X₀ n) : Tor.val X₀ (x + y) = Tor.val X₀ x + Tor.val X₀ y := rfl
theorem Tor.val_zero {n : ℕ} : Tor.val X₀ (0 : Tor X₀ n) = 0 := rfl
theorem Tor.smul_val {n : ℕ} (x : Tor X₀ n) : (n : ℤ) • Tor.val X₀ x = 0 := ((torEquiv X₀ n) x).2

def Tor.mk {n : ℕ} (P : Pt X₀) (hP : (n : ℤ) • P = 0) : Tor X₀ n :=
  (torEquiv X₀ n).symm ⟨P, (Submodule.mem_torsionBy_iff _ _).mpr hP⟩

@[scoped simp] theorem Tor.val_mk {n : ℕ} (P : Pt X₀) (hP : (n : ℤ) • P = 0) : Tor.val X₀ (Tor.mk X₀ P hP) = P := rfl

p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor"

def resAdd (n : ℕ) (r : ↥(rationalEndSubring κ X₀)) : Tor X₀ n →+ Tor X₀ n where
  toFun x := Tor.mk X₀ ((r : AddMonoid.End (Pt X₀)) (Tor.val X₀ x)) (by
    rw [← map_zsmul, Tor.smul_val, map_zero])
  map_zero' := Tor.ext X₀ (by simp [Tor.val_zero])
  map_add' x y := Tor.ext X₀ (by simp [Tor.val_add, map_add])

@[scoped simp] theorem val_resAdd (n : ℕ) (r : ↥(rationalEndSubring κ X₀)) (x : Tor X₀ n) :
    Tor.val X₀ (resAdd X₀ n r x) = (r : AddMonoid.End (Pt X₀)) (Tor.val X₀ x) := rfl

def res (n : ℕ) [NeZero n] : ↥(rationalEndSubring κ X₀) →+* Module.End (ZMod n) (Tor X₀ n) where
  toFun r := (resAdd X₀ n r).toZModLinearMap n
  map_one' := LinearMap.ext fun x => Tor.ext X₀ rfl
  map_mul' r s := LinearMap.ext fun x => Tor.ext X₀ rfl
  map_zero' := LinearMap.ext fun x => Tor.ext X₀ rfl
  map_add' r s := LinearMap.ext fun x => Tor.ext X₀ rfl

@[scoped simp] theorem val_res (n : ℕ) [NeZero n] (r : ↥(rationalEndSubring κ X₀)) (x : Tor X₀ n) :
    Tor.val X₀ (res X₀ n r x) = (r : AddMonoid.End (Pt X₀)) (Tor.val X₀ x) := rfl

end Torsion
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor"

section Rank

variable {κ : Type*} [Field κ] [DecidableEq κ] (X₀ : WeierstrassCurve κ) {a b : ℚ}

theorem nonempty_linearEquiv_fin_four {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    Nonempty (↥(rationalEndSubring κ X₀) ≃ₗ[ℤ] (Fin 4 → ℤ)) := by
  obtain ⟨B, hBmem, hBspan⟩ := hΛ.exists_basis_span_eq
  have hex : ∀ i, ∃ r : ↥(rationalEndSubring κ X₀), θ r = B i := fun i => by
    have : B i ∈ Set.range θ := by rw [hθΛ]; exact hBmem i
    exact this
  choose bR hbR using hex
  have hθsum : ∀ g : Fin 4 → ℤ, θ (∑ i, g i • bR i) = ∑ i, (g i : ℚ) • B i := by
    intro g
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hbR, Int.cast_smul_eq_zsmul]
  have hli : LinearIndependent ℤ bR := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, (g i : ℚ) • B i = 0 := by rw [← hθsum, hg, map_zero]
    have := Fintype.linearIndependent_iff.mp B.linearIndependent (fun i => (g i : ℚ)) h1 i
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range bR) := by
    intro r _
    have hr : θ r ∈ Submodule.span ℤ (Set.range B) := by
      rw [hBspan, ← SetLike.mem_coe, ← hθΛ]; exact ⟨r, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hr
    obtain ⟨c, hc⟩ := hr
    have : r = ∑ i, c i • bR i := by
      apply hθ
      rw [hθsum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨(Module.Basis.mk hli hsp).equivFun⟩

variable [IsAlgClosed κ]

theorem exists_eq_mul_natCast_of_forall [X₀.IsElliptic] {n : ℕ} (hn : (n : κ) ≠ 0)
    (r : ↥(rationalEndSubring κ X₀))
    (hr : ∀ P : Pt X₀, (n : ℤ) • P = 0 → (r : AddMonoid.End (Pt X₀)) P = 0) :
    ∃ s : ↥(rationalEndSubring κ X₀), r = s * n := by
  have hrat : ((r : AddMonoid.End (Pt X₀)) : Pt X₀ →+ Pt X₀) ∈ rationalHomSet κ X₀ X₀ :=
    mem_rationalHomSet_of_mem_rationalEndSubring X₀ r.2
  obtain ⟨β, hβ, hβr⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ X₀ X₀ hn hrat hr
  refine ⟨⟨β, Subring.subset_closure hβ⟩, Subtype.ext ?_⟩
  apply AddMonoidHom.ext
  intro P
  rw [hβr P]
  change (n : ℤ) • β P = β ((n : AddMonoid.End (Pt X₀)) P)
  rw [AddMonoid.End.natCast_apply, map_nsmul, natCast_zsmul]

end Rank
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor"

section Count

variable {κ : Type*} [Field κ] [DecidableEq κ] [IsAlgClosed κ] (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
variable {a b : ℚ}

theorem free_finite_and_card_end_le {n : ℕ} [NeZero n] (e : ZMod n × ZMod n ≃+ Tor X₀ n) :
    Module.Free (ZMod n) (Tor X₀ n) ∧ Module.Finite (ZMod n) (Tor X₀ n) ∧
      Finite (Module.End (ZMod n) (Tor X₀ n)) ∧ Nat.card (Module.End (ZMod n) (Tor X₀ n)) ≤ n ^ 4 := by
  let e' : (ZMod n × ZMod n) ≃ₗ[ZMod n] Tor X₀ n := e.toLinearEquiv fun c x => ZMod.map_smul e c x
  haveI hfree : Module.Free (ZMod n) (Tor X₀ n) := Module.Free.of_equiv e'
  haveI hfin : Module.Finite (ZMod n) (Tor X₀ n) := Module.Finite.equiv e'
  haveI : Finite (Tor X₀ n) := Module.finite_of_finite (ZMod n)
  haveI hfinE : Finite (Module.End (ZMod n) (Tor X₀ n)) :=
    Finite.of_injective (β := Tor X₀ n → Tor X₀ n) (fun f => (f : Tor X₀ n → Tor X₀ n))
      (fun f g h => LinearMap.ext (congrFun h))
  refine ⟨hfree, hfin, hfinE, ?_⟩

  let g₁ : Tor X₀ n := e (1, 0)
  let g₂ : Tor X₀ n := e (0, 1)
  have hdet : Function.Injective fun f : Module.End (ZMod n) (Tor X₀ n) => (f g₁, f g₂) := by
    intro f f' hff'
    simp only [Prod.mk.injEq] at hff'
    apply LinearMap.ext
    intro m
    obtain ⟨⟨c₁, c₂⟩, rfl⟩ := e.surjective m
    have hm : e (c₁, c₂) = c₁ • g₁ + c₂ • g₂ := by
      have : ((c₁, c₂) : ZMod n × ZMod n) = c₁ • (1, 0) + c₂ • (0, 1) := by ext <;> simp
      rw [this, map_add]
      change e' (c₁ • (1, 0)) + e' (c₂ • (0, 1)) = _
      rw [map_smul, map_smul]
      rfl
    rw [hm, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hff'.1, hff'.2]
  have hcardT : Nat.card (Tor X₀ n) = n ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]; ring
  calc Nat.card (Module.End (ZMod n) (Tor X₀ n))
      ≤ Nat.card (Tor X₀ n × Tor X₀ n) := Nat.card_le_card_of_injective _ hdet
    _ = n ^ 4 := by rw [Nat.card_prod, hcardT]; ring

theorem res_surjective {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {n : ℕ} [NeZero n] (hn : (n : κ) ≠ 0)
    (e : ZMod n × ZMod n ≃+ Tor X₀ n) :
    Function.Surjective (res X₀ n) := by
  obtain ⟨-, -, hfinE, hcardE⟩ := free_finite_and_card_end_le X₀ e
  haveI := hfinE
  obtain ⟨eR⟩ := nonempty_linearEquiv_fin_four X₀ hΛ θ hθ hθΛ

  let ψ : ↥(rationalEndSubring κ X₀) →+ (Fin 4 → ZMod n) :=
    { toFun := fun r i => ((eR r i : ℤ) : ZMod n)
      map_zero' := by ext i; simp
      map_add' := fun r s => by ext i; simp }
  have hψ : ∀ r i, ψ r i = ((eR r i : ℤ) : ZMod n) := fun r i => rfl
  have hψs : Function.Surjective ψ := by
    intro v
    refine ⟨eR.symm fun i => ((v i).val : ℤ), ?_⟩
    ext i
    rw [hψ, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_zmod_val]
  set ρ := res X₀ n with hρ

  have hker : ρ.toAddMonoidHom.ker = ψ.ker := by
    ext r
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    constructor
    · intro h0
      have hkill : ∀ P : Pt X₀, (n : ℤ) • P = 0 → (r : AddMonoid.End (Pt X₀)) P = 0 := by
        intro P hP
        have := congrArg (Tor.val X₀) (LinearMap.congr_fun h0 (Tor.mk X₀ P hP))
        simp at this
        exact this
      obtain ⟨s, rfl⟩ := exists_eq_mul_natCast_of_forall X₀ hn r hkill
      ext i
      have e1 : s * (n : ↥(rationalEndSubring κ X₀)) = (n : ℤ) • s := by
        rw [(Nat.cast_commute n s).eq.symm, ← nsmul_eq_mul, natCast_zsmul]
      rw [hψ, e1, map_zsmul, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
        zero_mul, Pi.zero_apply]
    · intro h0
      have hdvd : ∀ i, (n : ℤ) ∣ eR r i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hψ, h0, Pi.zero_apply]
      choose w hw using hdvd
      have hr : r = (n : ℤ) • eR.symm w := by
        apply eR.injective
        rw [map_zsmul, LinearEquiv.apply_symm_apply]
        ext i
        rw [hw i, Pi.smul_apply, smul_eq_mul]
      rw [hr, map_zsmul]
      apply LinearMap.ext
      intro x
      rw [LinearMap.smul_apply, LinearMap.zero_apply, natCast_zsmul, nsmul_eq_zero X₀ n]

  have hcardR : Nat.card ρ.toAddMonoidHom.range = n ^ 4 := by
    have h1 := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ρ.toAddMonoidHom).toEquiv
    have h2 := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv
    rw [← h1, hker, h2, AddMonoidHom.range_eq_top.mpr hψs, AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have htop : ρ.toAddMonoidHom.range = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    refine le_antisymm (AddSubgroup.card_le_card_addGroup _) ?_
    rw [hcardR]
    exact hcardE
  intro f
  have hf : f ∈ ρ.toAddMonoidHom.range := by rw [htop]; exact AddSubgroup.mem_top f
  obtain ⟨r, hr⟩ := hf
  exact ⟨r, hr⟩

end Count
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor"

section Main

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem main (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (L : Ideal ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (n : ℕ) (hn : (n : κ) ≠ 0) (hnL : (n : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) ∈ L)
    (r : ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (hr : ∀ P : (X₀.baseChange κ).toAffine.Point,
      (∀ l ∈ L, (l : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) →
        (r : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) :
    r ∈ L := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  haveI : NeZero n := ⟨hn0⟩

  obtain ⟨e₀⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := κ) X₀ hn
  let e : ZMod n × ZMod n ≃+ Tor X₀ n := e₀.trans (torEquiv X₀ n).symm
  obtain ⟨hfree, hfin, hfinE, -⟩ := free_finite_and_card_end_le X₀ e
  haveI := hfree
  haveI := hfin
  set ρ := res X₀ n with hρ
  have hρs : Function.Surjective ρ := res_surjective X₀ hΛ θ hθ hθΛ hn e

  let J : Ideal (Module.End (ZMod n) (Tor X₀ n)) := Ideal.map ρ L
  have hJ : ∀ j, j ∈ J ↔ ∃ l ∈ L, ρ l = j := fun j => Ideal.mem_map_iff_of_surjective ρ hρs

  have hb : ∀ m : Tor X₀ n, (∀ j ∈ J, j m = 0) → ρ r m = 0 := by
    intro m hm
    apply Tor.ext X₀
    rw [val_res, Tor.val_zero]
    refine hr _ fun l hl => ?_
    have := hm (ρ l) ((hJ _).mpr ⟨l, hl, rfl⟩)
    have := congrArg (Tor.val X₀) this
    rwa [val_res, Tor.val_zero] at this
  have hmem : ρ r ∈ J := Module.End.mem_ideal_of_forall_apply_eq_zero_zmod J (ρ r) hb
  obtain ⟨l, hl, hlr⟩ := (hJ _).mp hmem

  have hkill : ∀ P : Pt X₀, (n : ℤ) • P = 0 → ((r - l : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt X₀)) P = 0 := by
    intro P hP
    have h0 : ρ (r - l) = 0 := by rw [map_sub, hlr, sub_self]
    have := congrArg (Tor.val X₀) (LinearMap.congr_fun h0 (Tor.mk X₀ P hP))
    simp at this
    exact this
  obtain ⟨s, hs⟩ := exists_eq_mul_natCast_of_forall X₀ hn (r - l) hkill
  have : r = l + s * n := by rw [← hs]; abel
  rw [this]
  exact L.add_mem hl (L.mul_mem_left s hnL)

end Main
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor"

end KernelIdealFiniteLevel
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel.Tor P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve.KernelIdealFiniteLevel P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero.WeierstrassCurve"

theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (L : Ideal ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (n : ℕ) (hn : (n : κ) ≠ 0) (hnL : (n : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) ∈ L)
    (r : ↥(WeierstrassCurve.rationalEndSubring κ X₀))
    (hr : ∀ P : (X₀.baseChange κ).toAffine.Point,
      (∀ l ∈ L, (l : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) →
        (r : AddMonoid.End (X₀.baseChange κ).toAffine.Point) P = 0) :
    r ∈ L :=
  WeierstrassCurve.KernelIdealFiniteLevel.main X₀ a b Λ hΛ θ hθ hθΛ L n hn hnL r hr

end S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero (solution)
