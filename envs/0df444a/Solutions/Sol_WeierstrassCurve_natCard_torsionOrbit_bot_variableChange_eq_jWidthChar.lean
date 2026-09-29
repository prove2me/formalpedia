-- Prove2me | solution 1 for WeierstrassCurve.natCard_torsionOrbit_bot_variableChange_eq_jWidthChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/682357c4-1b1e-52f9-b83e-bf73fd0f466e

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_one_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace OrbitWidthGlue

variable {K : Type*} [Field K] [DecidableEq K]

theorem vcInvFun_heq_of_heq (C : VariableChange K) {V V' : WeierstrassCurve.Affine K} (hV : V = V')
    (T : V.Point) (T' : V'.Point) (hT : HEq T T') :
    HEq (Point.vcInvFun C V T) (Point.vcInvFun C V' T') := by
  subst hV
  have := eq_of_heq hT
  subst this
  rfl

theorem heq_add_of_heq {V V' : WeierstrassCurve.Affine K} (hV : V = V')
    (a b : V.Point) (a' b' : V'.Point) (ha : HEq a a') (hb : HEq b b') :
    HEq (a + b) (a' + b') := by
  subst hV
  have h1 := eq_of_heq ha
  have h2 := eq_of_heq hb
  subst h1 h2
  rfl

theorem equivSymm_heq (C : VariableChange K) {W V : WeierstrassCurve.Affine K} (h : C • W = V) (T : W.Point) :
    HEq (Point.vcInvFun C W T) ((Point.equivOfVariableChangeEq h).symm T) := by
  subst h
  rfl

section Action

variable (E : WeierstrassCurve K)

noncomputable def act (γ : ↥(MulAction.stabilizer (VariableChange K) E)) : E.toAffine.Point ≃ E.toAffine.Point :=
  (Point.equivOfVariableChangeEq (C := (γ : VariableChange K)) (W := E.toAffine) (V := E.toAffine)
    (MulAction.mem_stabilizer_iff.mp γ.2)).symm

theorem act_heq (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) :
    HEq (Point.vcInvFun (γ : VariableChange K) E.toAffine T) (act E γ T) :=
  equivSymm_heq _ _ _

theorem heq_act_iff_eq (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T T' : E.toAffine.Point) :
    HEq (Point.vcInvFun (γ : VariableChange K) E.toAffine T) T' ↔ act E γ T = T' := by
  constructor
  · intro h
    exact eq_of_heq ((act_heq E γ T).symm.trans h)
  · intro h
    rw [← h]
    exact act_heq E γ T

theorem act_one (T : E.toAffine.Point) : act E 1 T = T :=
  eq_of_heq ((act_heq E 1 T).symm.trans (WeierstrassCurve.Affine.Point.vcInvFun_one_heq E.toAffine T))

theorem act_mul (γ δ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) :
    act E (γ * δ) T = act E γ (act E δ T) := by
  apply eq_of_heq
  have hδ : (δ : VariableChange K) • E.toAffine = E.toAffine := MulAction.mem_stabilizer_iff.mp δ.2
  have h1 : HEq (act E (γ * δ) T) (Point.vcInvFun ((γ : VariableChange K) * (δ : VariableChange K)) E.toAffine T) :=
    (act_heq E (γ * δ) T).symm
  have h2 := WeierstrassCurve.Affine.Point.vcInvFun_mul_heq (γ : VariableChange K) (δ : VariableChange K) E.toAffine T
  have h3 : HEq (Point.vcInvFun (γ : VariableChange K) ((δ : VariableChange K) • E.toAffine)
      (Point.vcInvFun (δ : VariableChange K) E.toAffine T))
      (Point.vcInvFun (γ : VariableChange K) E.toAffine (act E δ T)) :=
    vcInvFun_heq_of_heq _ hδ _ _ (act_heq E δ T)
  exact h1.trans (h2.trans (h3.trans (act_heq E γ _)))

noncomputable scoped instance pointAction : MulAction ↥(MulAction.stabilizer (VariableChange K) E) E.toAffine.Point where
  smul γ T := act E γ T
  one_smul := act_one E
  mul_smul := act_mul E

theorem smul_def (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) : γ • T = act E γ T := rfl

theorem smul_add' (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T T' : E.toAffine.Point) :
    γ • (T + T') = γ • T + γ • T' := by
  rw [smul_def, smul_def, smul_def]
  apply eq_of_heq
  have hγ : (γ : VariableChange K) • E.toAffine = E.toAffine := MulAction.mem_stabilizer_iff.mp γ.2
  refine (act_heq E γ (T + T')).symm.trans ?_
  rw [WeierstrassCurve.Affine.Point.vcInvFun_add]
  exact heq_add_of_heq hγ _ _ _ _ (act_heq E γ T) (act_heq E γ T')

noncomputable def actAdd (γ : ↥(MulAction.stabilizer (VariableChange K) E)) : E.toAffine.Point ≃+ E.toAffine.Point :=
  { act E γ with map_add' := smul_add' E γ }

theorem actAdd_apply (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) : actAdd E γ T = γ • T := rfl

theorem smul_nsmul' (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (k : ℕ) (T : E.toAffine.Point) :
    γ • (k • T) = k • (γ • T) := by
  rw [← actAdd_apply, map_nsmul, actAdd_apply]

theorem smul_neg'' (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) :
    γ • (-T) = -(γ • T) := by
  rw [← actAdd_apply, map_neg, actAdd_apply]

theorem addOrderOf_smul (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (T : E.toAffine.Point) :
    addOrderOf (γ • T) = addOrderOf T := by
  rw [← actAdd_apply]
  exact AddEquiv.addOrderOf_eq (actAdd E γ) T

end Action

end OrbitWidthGlue
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar.OrbitWidthGlue"

namespace OrbitWidthGlue

variable {K : Type*} [Field K] [DecidableEq K]

section Level

variable (E : WeierstrassCurve K) (M : ℕ) [NeZero M]

theorem mem_units_iff (u : (ZMod M)ˣ) :
    u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ↔ u = 1 ∨ u = -1 := by
  rw [bot_sup_eq, Subgroup.mem_zpowers_iff]
  have h2 : (-1 : (ZMod M)ˣ) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    simp
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem neg_one_val_smul (hM : 2 ≤ M) (P : E.toAffine.Point) (hP : addOrderOf P = M) :
    ((-1 : (ZMod M)ˣ) : ZMod M).val • P = -P := by
  haveI : Fact (1 < M) := ⟨hM⟩
  rw [Units.val_neg, Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have h : (M - 1) • P + P = 0 := by
    rw [← succ_nsmul, Nat.sub_add_cancel (by omega), ← hP, addOrderOf_nsmul_eq_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem one_val_smul (hM : 2 ≤ M) (P : E.toAffine.Point) :
    ((1 : (ZMod M)ˣ) : ZMod M).val • P = P := by
  haveI : Fact (1 < M) := ⟨hM⟩
  rw [Units.val_one, ZMod.val_one, one_smul]

theorem levelSet_eq (hM : 2 ≤ M) (P : E.toAffine.Point) (hP : addOrderOf P = M) :
    {T : E.toAffine.Point | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
      T = (u : ZMod M).val • P} = {P, -P} := by
  ext T
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, mem_units_iff]
  constructor
  · rintro ⟨u, hu | hu, rfl⟩
    · left; subst hu; exact one_val_smul E M hM P
    · right; subst hu; exact neg_one_val_smul E M hM P hP
  · rintro (rfl | rfl)
    · exact ⟨1, Or.inl rfl, (one_val_smul E M hM _).symm⟩
    · exact ⟨-1, Or.inr rfl, (neg_one_val_smul E M hM _ hP).symm⟩

theorem image_levelSet (hM : 2 ≤ M) (γ : ↥(MulAction.stabilizer (VariableChange K) E))
    (P : E.toAffine.Point) (hP : addOrderOf P = M) :
    (fun T => γ • T) '' {T : E.toAffine.Point | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
      T = (u : ZMod M).val • P} =
    {T : E.toAffine.Point | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
      T = (u : ZMod M).val • (γ • P)} := by
  have hP' : addOrderOf (γ • P) = M := by rw [addOrderOf_smul, hP]
  rw [levelSet_eq E M hM P hP, levelSet_eq E M hM (γ • P) hP', Set.image_pair, smul_neg'']

noncomputable def actX (hM : 2 ≤ M) (γ : ↥(MulAction.stabilizer (VariableChange K) E))
    (s : {s : Set E.toAffine.Point // ∃ P : E.toAffine.Point, addOrderOf P = M ∧
      s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
        T = (u : ZMod M).val • P}}) :
    {s : Set E.toAffine.Point // ∃ P : E.toAffine.Point, addOrderOf P = M ∧
      s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
        T = (u : ZMod M).val • P}} :=
  ⟨(fun T => γ • T) '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    refine ⟨γ • P, by rw [addOrderOf_smul, hP], ?_⟩
    rw [hs, image_levelSet E M hM γ P hP]⟩

theorem actX_val (hM : 2 ≤ M) (γ : ↥(MulAction.stabilizer (VariableChange K) E)) (s) :
    (actX E M hM γ s).1 = (fun T => γ • T) '' s.1 := rfl

noncomputable def levelAction (hM : 2 ≤ M) :
    MulAction ↥(MulAction.stabilizer (VariableChange K) E)
      {s : Set E.toAffine.Point // ∃ P : E.toAffine.Point, addOrderOf P = M ∧
        s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
          T = (u : ZMod M).val • P}} where
  smul γ s := actX E M hM γ s
  one_smul s := by
    apply Subtype.ext
    change (fun T => (1 : ↥(MulAction.stabilizer (VariableChange K) E)) • T) '' s.1 = s.1
    simp only [one_smul, Set.image_id']
  mul_smul γ δ s := by
    apply Subtype.ext
    change (fun T => (γ * δ) • T) '' s.1 = (fun T => γ • T) '' ((fun T => δ • T) '' s.1)
    rw [Set.image_image]
    simp only [mul_smul]

end Level
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar.OrbitWidthGlue"

end OrbitWidthGlue
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar.OrbitWidthGlue"

open OrbitWidthGlue in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hMK : (M : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (s : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}) :
    Nat.card {s' : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}} //
        ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ s'.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'}
      = ModularCurve.jWidthChar p E₀.j := by
  classical
  have h2 : 2 ≤ M := by omega
  letI := OrbitWidthGlue.levelAction E₀ M h2

  have hsub : ∀ (g : ↥(MulAction.stabilizer (VariableChange K) E₀))
      (s₁ s₂ : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}),
      (∀ T ∈ s₂.1, g • T ∈ s₁.1) → g • s₂ = s₁ := by
    intro g s₁ s₂ h
    apply Subtype.ext
    rw [show (g • s₂).1 = (fun T => g • T) '' s₂.1 from rfl]
    obtain ⟨P, hP, hs⟩ := s₁.2
    obtain ⟨P', hP', hs'⟩ := s₂.2
    have e1 := levelSet_eq E₀ M h2 P hP
    have e2 := levelSet_eq E₀ M h2 P' hP'
    have hmem : g • P' ∈ ({P, -P} : Set E₀.toAffine.Point) := by
      rw [← e1, ← hs]
      apply h
      rw [hs', e2]
      exact Set.mem_insert _ _
    rw [hs', e2, Set.image_pair, smul_neg'', hs, e1]
    rcases hmem with h1 | h1
    · rw [h1]
    · rw [Set.mem_singleton_iff] at h1
      rw [h1, neg_neg, Set.pair_comm]

  have hF : ∀ s' : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}},
      (∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ s'.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ↔
        s' ∈ MulAction.orbit ↥(MulAction.stabilizer (VariableChange K) E₀) s := by
    intro s'
    constructor
    · rintro ⟨γ, hγ, h⟩
      let g : ↥(MulAction.stabilizer (VariableChange K) E₀) := ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩
      have hg : g • s' = s := hsub g s s' (fun T hT => by
        obtain ⟨T', hT', hh⟩ := h T hT
        rw [smul_def, (heq_act_iff_eq E₀ g T T').mp hh]
        exact hT')
      rw [MulAction.mem_orbit_iff]
      exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
    · intro hmem
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
      refine ⟨((g⁻¹ : ↥(MulAction.stabilizer (VariableChange K) E₀)) : VariableChange K),
        MulAction.mem_stabilizer_iff.mp (g⁻¹).2, fun T hT => ⟨g⁻¹ • T, ?_, ?_⟩⟩
      · obtain ⟨T₀, hT₀, rfl⟩ := (show T ∈ (fun T => g • T) '' s.1 from hT)
        rw [inv_smul_smul]
        exact hT₀
      · exact (heq_act_iff_eq E₀ g⁻¹ T _).mpr rfl

  have hS : ∀ g : ↥(MulAction.stabilizer (VariableChange K) E₀),
      (∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (g : VariableChange K) E₀.toAffine T) T') ↔
        g ∈ MulAction.stabilizer ↥(MulAction.stabilizer (VariableChange K) E₀) s := by
    intro g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact hsub g s s (fun T hT => by
        obtain ⟨T', hT', hh⟩ := h T hT
        rw [smul_def, (heq_act_iff_eq E₀ g T T').mp hh]
        exact hT')
    · intro h T hT
      refine ⟨g • T, ?_, (heq_act_iff_eq E₀ g T _).mpr rfl⟩
      rw [← h]
      exact ⟨T, hT, rfl⟩

  have e1 := Equiv.subtypeEquivRight hF
  have e2 := Equiv.subtypeEquivRight hS
  have hstab2 := WeierstrassCurve.natCard_stabilizer_torsionOrbit_bot_eq_two K p M hM hMK E₀ s
  rw [Nat.card_congr e2] at hstab2
  have haut := WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar K p E₀
  have horb := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer ↥(MulAction.stabilizer (VariableChange K) E₀) s)
  rw [Nat.card_congr e1, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ s)]
  rw [hstab2, haut] at horb
  omega

end S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar
end P2MW
export P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar (solution)
