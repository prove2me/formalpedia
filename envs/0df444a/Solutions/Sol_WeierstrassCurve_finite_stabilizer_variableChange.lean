-- Prove2me | solution 1 for WeierstrassCurve.finite_stabilizer_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8697abe3-c915-52f3-b014-d6370f63d5e0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange

noncomputable section

open WeierstrassCurve Polynomial MulAction

namespace AutFinitePort

section PolyTools

variable {F : Type*} [Field F]

theorem ccgaf_quad_ne_zero (b c : F) : (X ^ 2 + C b * X - C c : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 2 + C b * X - C c : F[X]).coeff 2 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_quad_eval (b c t : F) :
    (X ^ 2 + C b * X - C c : F[X]).eval t = t ^ 2 + b * t - c := by
  simp

theorem ccgaf_cubic_ne_zero (b c : F) : (X ^ 3 + C b * X ^ 2 + C c * X : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 3 + C b * X ^ 2 + C c * X : F[X]).coeff 3 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_cubic_eval (b c r : F) :
    (X ^ 3 + C b * X ^ 2 + C c * X : F[X]).eval r = r ^ 3 + b * r ^ 2 + c * r := by
  simp

theorem ccgaf_quart_ne_zero (a : F) : (X ^ 4 + C a * X : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 4 + C a * X : F[X]).coeff 4 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_quart_eval (a s : F) : (X ^ 4 + C a * X : F[X]).eval s = s ^ 4 + a * s := by
  simp

end PolyTools

section CoefficientIdentities

variable {F : Type*} [Field F]

theorem ccgaf_coeff_eqs (E : WeierstrassCurve F) (γ : VariableChange F)
    (hst : γ • E = E) (hu : γ.u = 1) :
    2 * γ.s = 0
    ∧ (- γ.s * E.a₁ + 3 * γ.r - γ.s ^ 2 = 0)
    ∧ (γ.r * E.a₁ + 2 * γ.t = 0)
    ∧ (- γ.s * E.a₃ + 2 * γ.r * E.a₂ - (γ.t + γ.r * γ.s) * E.a₁ + 3 * γ.r ^ 2
        - 2 * γ.s * γ.t = 0)
    ∧ (γ.r * E.a₄ + γ.r ^ 2 * E.a₂ + γ.r ^ 3 - γ.t * E.a₃ - γ.t ^ 2
        - γ.r * γ.t * E.a₁ = 0) := by
  have hu' : ((γ.u⁻¹ : Fˣ) : F) = 1 := by rw [hu]; simp
  have h1 := congrArg WeierstrassCurve.a₁ hst
  rw [variableChange_a₁, hu', one_mul] at h1
  have h2 := congrArg WeierstrassCurve.a₂ hst
  rw [variableChange_a₂, hu', one_pow, one_mul] at h2
  have h3 := congrArg WeierstrassCurve.a₃ hst
  rw [variableChange_a₃, hu', one_pow, one_mul] at h3
  have h4 := congrArg WeierstrassCurve.a₄ hst
  rw [variableChange_a₄, hu', one_pow, one_mul] at h4
  have h6 := congrArg WeierstrassCurve.a₆ hst
  rw [variableChange_a₆, hu', one_pow, one_mul] at h6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4
  · linear_combination h6

end CoefficientIdentities

section KernelFiniteness

variable {F : Type*} [Field F]

theorem ccgaf_finite_unipotentStabilizer (E : WeierstrassCurve F) :
    Finite {γ : VariableChange F // γ • E = E ∧ γ.u = 1} := by
  classical
  by_cases hchar2 : (2 : F) = 0
  ·
    have h31 : (3 : F) = 1 := by linear_combination hchar2
    by_cases ha1 : E.a₁ = 0
    ·

      let P : F[X] := X ^ 4 + C E.a₃ * X
      have hP : P ≠ 0 := ccgaf_quart_ne_zero E.a₃
      let κ : F → F := fun s => (s ^ 2) * E.a₄ + (s ^ 2) ^ 2 * E.a₂ + (s ^ 2) ^ 3
      let Q : F → F[X] := fun s => X ^ 2 + C E.a₃ * X - C (κ s)
      have hQ : ∀ s, Q s ≠ 0 := fun s => ccgaf_quad_ne_zero E.a₃ (κ s)
      let T : Finset (F × F) :=
        (P.roots.toFinset).biUnion (fun s => ((Q s).roots.toFinset).image (fun t => (s, t)))
      refine Finite.of_injective
        (fun γ => (⟨(γ.1.s, γ.1.t), ?_⟩ : {p : F × F // p ∈ T})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, e2, -, e4, e6⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [ha1, h31] at e2
        have hr : γ.r = γ.s ^ 2 := by linear_combination e2
        rw [ha1, hchar2, h31, hr] at e4
        have hs : P.IsRoot γ.s := by
          rw [IsRoot.def, ccgaf_quart_eval]
          linear_combination e4 + (E.a₃ * γ.s) * hchar2
        rw [ha1, hr] at e6
        have ht : (Q γ.s).IsRoot γ.t := by
          rw [IsRoot.def, ccgaf_quad_eval]
          linear_combination -e6
        simp only [T, Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_image]
        exact ⟨γ.s, (mem_roots hP).mpr hs, γ.t, (mem_roots (hQ _)).mpr ht, rfl⟩
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        obtain ⟨hs, ht⟩ := heq
        obtain ⟨-, e2, -, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        obtain ⟨-, e2', -, -, -⟩ := ccgaf_coeff_eqs E γ' hst' hu'
        rw [ha1, h31] at e2 e2'
        have hr : γ.r = γ.s ^ 2 := by linear_combination e2
        have hr' : γ'.r = γ'.s ^ 2 := by linear_combination e2'
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · rw [hr, hr', hs]
        · exact hs
        · exact ht
    ·
      refine Finite.of_injective
        (fun γ => (⟨γ.1.s, ?_⟩ : {x : F // x ∈ ({0, -E.a₁} : Finset F)})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, e2, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [hchar2, zero_mul, add_zero] at e3
        have hr : γ.r = 0 := (mul_eq_zero.mp e3).resolve_right ha1
        rw [h31, hr] at e2
        have hss : γ.s * (E.a₁ + γ.s) = 0 := by linear_combination -e2
        rcases mul_eq_zero.mp hss with h0 | h0
        · simp [h0]
        · have hsa : γ.s = -E.a₁ := by linear_combination h0
          simp [hsa]
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq] at heq
        obtain ⟨-, -, e3, e4, -⟩ := ccgaf_coeff_eqs E γ hst hu
        obtain ⟨-, -, e3', e4', -⟩ := ccgaf_coeff_eqs E γ' hst' hu'
        rw [hchar2, zero_mul, add_zero] at e3 e3'
        have hr : γ.r = 0 := (mul_eq_zero.mp e3).resolve_right ha1
        have hr' : γ'.r = 0 := (mul_eq_zero.mp e3').resolve_right ha1
        rw [hchar2, h31, hr] at e4
        rw [hchar2, h31, hr'] at e4'
        have ht : γ.t * E.a₁ = γ'.t * E.a₁ := by
          rw [heq] at e4
          linear_combination e4' - e4
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · rw [hr, hr']
        · exact heq
        · exact mul_right_cancel₀ ha1 ht
  ·
    have hs0 : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ.s = 0 := by
      intro γ hst hu
      obtain ⟨e1, -, -, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
      exact (mul_eq_zero.mp e1).resolve_left hchar2
    by_cases hchar3 : (3 : F) = 0
    ·
      set τ : F := -E.a₁ / 2 with hτ
      let C₃ : F[X] :=
        X ^ 3 + C (E.a₂ - τ ^ 2 - τ * E.a₁) * X ^ 2 + C (E.a₄ - τ * E.a₃) * X
      have hC₃ : C₃ ≠ 0 := ccgaf_cubic_ne_zero _ _
      have ht : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ.t = τ * γ.r := by
        intro γ hst hu
        obtain ⟨-, -, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [hτ]
        field_simp
        linear_combination e3
      refine Finite.of_injective
        (fun γ => (⟨γ.1.r, ?_⟩ : {x : F // x ∈ C₃.roots.toFinset})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, -, -, -, e6⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [ht γ hst hu] at e6
        have hr : C₃.IsRoot γ.r := by
          rw [IsRoot.def, ccgaf_cubic_eval]
          linear_combination e6
        rw [Multiset.mem_toFinset]
        exact (mem_roots hC₃).mpr hr
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq] at heq
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · exact heq
        · rw [hs0 γ hst hu, hs0 γ' hst' hu']
        · rw [ht γ hst hu, ht γ' hst' hu', heq]
    ·
      have hone : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ = 1 := by
        intro γ hst hu
        obtain ⟨-, e2, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        have hs : γ.s = 0 := hs0 γ hst hu
        rw [hs] at e2
        have hr : γ.r = 0 := by
          have h3r : 3 * γ.r = 0 := by linear_combination e2
          exact (mul_eq_zero.mp h3r).resolve_left hchar3
        rw [hr] at e3
        have ht : γ.t = 0 := by
          have h2t : 2 * γ.t = 0 := by linear_combination e3
          exact (mul_eq_zero.mp h2t).resolve_left hchar2
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu]; rfl
        · rw [hr]; rfl
        · rw [hs]; rfl
        · rw [ht]; rfl
      haveI : Subsingleton {γ : VariableChange F // γ • E = E ∧ γ.u = 1} :=
        ⟨fun ⟨γ, hγ⟩ ⟨γ', hγ'⟩ => Subtype.ext
          ((hone γ hγ.1 hγ.2).trans (hone γ' hγ'.1 hγ'.2).symm)⟩
      infer_instance

end KernelFiniteness

section StabilizerFiniteness

variable {F : Type*} [Field F]

def ccgaf_uHom : VariableChange F →* Fˣ where
  toFun γ := γ.u
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem ccgaf_uHom_apply (γ : VariableChange F) : ccgaf_uHom γ = γ.u := rfl

theorem ccgaf_u_pow_twelve (E : WeierstrassCurve F) [E.IsElliptic] (γ : VariableChange F)
    (hst : γ • E = E) : γ.u ^ 12 = 1 := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have h := congrArg WeierstrassCurve.Δ hst
  rw [variableChange_Δ] at h
  have h1 : ((γ.u⁻¹ : Fˣ) : F) ^ 12 = 1 :=
    mul_right_cancel₀ hΔ (h.trans (one_mul E.Δ).symm)
  have h2 : ((γ.u ^ 12)⁻¹ : Fˣ) = 1 := by
    rw [← inv_pow, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]
    exact h1
  simpa using h2

theorem ccgaf_stabilizer_finite (E : WeierstrassCurve F) [E.IsElliptic] :
    Finite ↥(MulAction.stabilizer (VariableChange F) E) := by
  classical
  let St := MulAction.stabilizer (VariableChange F) E
  let φ : ↥St →* Fˣ := (ccgaf_uHom (F := F)).comp St.subtype

  have hrange : φ.range ≤ rootsOfUnity 12 F := by
    rintro _ ⟨⟨γ, hγ⟩, rfl⟩
    rw [mem_rootsOfUnity]
    exact ccgaf_u_pow_twelve E γ (MulAction.mem_stabilizer_iff.mp hγ)
  haveI : Finite ↥(rootsOfUnity 12 F) := inferInstance
  haveI hR : Finite ↥φ.range :=
    Finite.of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)

  haveI hKtype : Finite {γ : VariableChange F // γ • E = E ∧ γ.u = 1} :=
    ccgaf_finite_unipotentStabilizer E
  haveI hK : Finite ↥φ.ker := by
    refine Finite.of_injective
      (fun γ => (⟨γ.1.1, ⟨MulAction.mem_stabilizer_iff.mp γ.1.2, ?_⟩⟩ :
        {γ : VariableChange F // γ • E = E ∧ γ.u = 1})) ?_
    · have h := γ.2
      rw [MonoidHom.mem_ker] at h
      exact h
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun (z : {γ : VariableChange F // γ • E = E ∧ γ.u = 1}) => z.1) h

  haveI : Finite (↥St ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := φ.ker)).symm

end StabilizerFiniteness

end AutFinitePort
p2m_reactivate "P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange.AutFinitePort"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange.AutFinitePort"

theorem solution (F : Type*) [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) :=
  AutFinitePort.ccgaf_stabilizer_finite E

end S_WeierstrassCurve_finite_stabilizer_variableChange
end P2MW
export P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange (solution)
