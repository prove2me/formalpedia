-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_torsionOrbit_bot_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1d91ea68-e843-5aae-b6f1-b706396e18e4

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_one_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace STAB2E100

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) : V'.Point := h ▸ P

theorem heq_iff_castPt_eq {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) (Q : V'.Point) :
    HEq P Q ↔ castPt h P = Q := by
  subst h; simp [castPt, heq_iff_eq]

theorem castPt_add {V V' : WeierstrassCurve.Affine K} (h : V = V') (P Q : V.Point) :
    castPt h (P + Q) = castPt h P + castPt h Q := by
  subst h; rfl

theorem castPt_neg {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) :
    castPt h (-P) = -castPt h P := by
  subst h; rfl

theorem castPt_zero {V V' : WeierstrassCurve.Affine K} (h : V = V') : castPt h (0 : V.Point) = 0 := by
  subst h; rfl

theorem castPt_castPt {V V' V'' : WeierstrassCurve.Affine K} (h : V = V') (h' : V' = V'') (P : V.Point) :
    castPt h' (castPt h P) = castPt (h.trans h') P := by
  subst h h'; rfl

section transport

variable (E : WeierstrassCurve K)

theorem toAffine_eq_of_smul_eq {γ : VariableChange K} (hγ : γ • E = E) : (γ • E).toAffine = E.toAffine :=
  congrArg WeierstrassCurve.toAffine hγ

def tr (γ : VariableChange K) (hγ : γ • E = E) (P : E.toAffine.Point) : E.toAffine.Point :=
  castPt (toAffine_eq_of_smul_eq E hγ) (Point.vcInvFun γ E.toAffine P)

theorem heq_vcInvFun_iff {γ : VariableChange K} (hγ : γ • E = E) (P Q : E.toAffine.Point) :
    HEq (Point.vcInvFun γ E.toAffine P) Q ↔ tr E γ hγ P = Q :=
  heq_iff_castPt_eq _ _ _

theorem tr_add {γ : VariableChange K} (hγ : γ • E = E) (P Q : E.toAffine.Point) :
    tr E γ hγ (P + Q) = tr E γ hγ P + tr E γ hγ Q := by
  unfold tr
  rw [Point.vcInvFun_add, castPt_add]

theorem tr_nsmul {γ : VariableChange K} (hγ : γ • E = E) (n : ℕ) (P : E.toAffine.Point) :
    tr E γ hγ (n • P) = n • tr E γ hγ P := by
  induction n with
  | zero => simp [tr, castPt_zero]
  | succ n ih => rw [succ_nsmul, tr_add, ih, succ_nsmul]

def negVC : VariableChange K := ⟨-1, 0, -E.a₁, -E.a₃⟩

theorem negVC_smul : negVC E • E = E := by
  ext <;> simp [negVC, WeierstrassCurve.variableChange_def] <;> ring

theorem tr_negVC (P : E.toAffine.Point) : tr E (negVC E) (negVC_smul E) P = -P := by
  rw [← heq_vcInvFun_iff]
  exact Point.vcInvFun_neg_heq_neg E P

theorem tr_one (P : E.toAffine.Point) : tr E 1 (one_smul _ E) P = P := by
  rw [← heq_vcInvFun_iff]
  exact Point.vcInvFun_one_heq E.toAffine P

theorem tr_mul {γ γ' : VariableChange K} (hγ : γ • E = E) (hγ' : γ' • E = E) (P : E.toAffine.Point) :
    tr E (γ * γ') ((mul_smul γ γ' E).trans (by rw [hγ', hγ])) P = tr E γ hγ (tr E γ' hγ' P) := by

  have h1 := Point.vcInvFun_mul_heq γ γ' E.toAffine P

  rw [← heq_vcInvFun_iff]
  refine h1.trans ?_

  have key : ∀ (V : WeierstrassCurve K) (hV : V = E) (Q : V.toAffine.Point),
      HEq (Point.vcInvFun γ V.toAffine Q) (tr E γ hγ (castPt (congrArg WeierstrassCurve.toAffine hV) Q)) := by
    intro V hV Q
    subst hV
    simp only [castPt]
    rw [heq_vcInvFun_iff]
  have := key (γ' • E) hγ' (Point.vcInvFun γ' E.toAffine P)
  exact this

end transport

section main

variable (E : WeierstrassCurve K)

theorem negVC_mul_negVC : negVC E * negVC E = 1 := by
  simp only [negVC, VariableChange.mul_def, VariableChange.one_def]
  congr 1 <;> simp <;> ring

theorem negVC_ne_one [E.IsElliptic] : negVC E ≠ 1 := by
  intro h
  have hu : (((negVC E).u : Kˣ) : K) = ((1 : VariableChange K).u : K) := by rw [h]
  have hs : (negVC E).s = (1 : VariableChange K).s := by rw [h]
  have ht : (negVC E).t = (1 : VariableChange K).t := by rw [h]
  simp only [negVC, VariableChange.one_def, Units.val_neg, Units.val_one, neg_eq_zero] at hu hs ht
  have h2 : (2 : K) = 0 := by linear_combination -hu
  have h4 : (4 : K) = 0 := by linear_combination 2 * h2
  have hb2 : E.b₂ = 0 := by rw [WeierstrassCurve.b₂, hs]; linear_combination E.a₂ * h4
  have hb4 : E.b₄ = 0 := by rw [WeierstrassCurve.b₄, hs, ht]; linear_combination E.a₄ * h2
  have hb6 : E.b₆ = 0 := by rw [WeierstrassCurve.b₆, ht]; linear_combination E.a₆ * h4
  have hΔ : E.Δ = 0 := by rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring
  exact E.isUnit_Δ.ne_zero hΔ

theorem nsmul_injOn {P : E.toAffine.Point} {M : ℕ} (hP : addOrderOf P = M) {m n : ℕ}
    (hm : m < M) (hn : n < M) (h : m • P = n • P) : m = n := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this hn hm h.symm (not_le.mp hmn).le).symm
  have h0 : (n - m) • P = 0 := by
    have : n • P = (n - m) • P + m • P := by rw [← add_nsmul, Nat.sub_add_cancel hmn]
    rw [← h] at this
    exact add_right_cancel (this.symm.trans (zero_add _).symm)
  have hdvd : M ∣ n - m := by rw [← hP]; exact addOrderOf_dvd_of_nsmul_eq_zero h0
  have : n - m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

theorem addOrderOf_le_three_of_tr_eq [E.IsElliptic] {γ : VariableChange K} (hγ : γ • E = E) (h1 : γ ≠ 1)
    (hneg : γ ≠ negVC E) {P : E.toAffine.Point} (hfix : tr E γ hγ P = P) {M : ℕ} (hP : addOrderOf P = M)
    (hM : 4 ≤ M) : False := by
  classical
  let F : Finset E.toAffine.Point := (Finset.range M).image (fun n => n • P)
  have hcard : F.card = M := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro m hm n hn hmn
    exact nsmul_injOn E hP (Finset.mem_range.mp hm) (Finset.mem_range.mp hn) hmn
  have hF : ∀ Q ∈ F, HEq (Point.vcInvFun γ E.toAffine Q) Q := by
    intro Q hQ
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hQ
    rw [heq_vcInvFun_iff E hγ, tr_nsmul, hfix]
  have := WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun E γ hγ h1 hneg F hF
  omega

theorem val_neg_one_smul {M : ℕ} [NeZero M] (hM1 : 1 < M) {P : E.toAffine.Point} (hP : addOrderOf P = M) :
    (((-1 : (ZMod M)ˣ) : ZMod M)).val • P = -P := by
  have hcast : ((-1 : (ZMod M)ˣ) : ZMod M) = ((M - 1 : ℕ) : ZMod M) := by
    rw [Units.val_neg, Units.val_one]
    have h : ((M - 1 : ℕ) : ZMod M) + 1 = 0 := by
      have : ((M - 1 : ℕ) : ZMod M) + 1 = ((M - 1 + 1 : ℕ) : ZMod M) := by push_cast; ring
      rw [this, Nat.sub_add_cancel hM1.le, ZMod.natCast_self]
    linear_combination -h
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h0 : (M - 1) • P + P = 0 := by
    rw [← succ_nsmul, Nat.sub_add_cancel hM1.le, ← hP, addOrderOf_nsmul_eq_zero]
  exact eq_neg_of_add_eq_zero_left h0

end main

end STAB2E100

open STAB2E100 in
theorem stab2_main
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hMK : (M : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (s : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}) :
    Nat.card {γ : ↥(MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) //
        ∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (γ : WeierstrassCurve.VariableChange K) E₀.toAffine T) T'} = 2 := by
  classical
  obtain ⟨P, hP, hs⟩ := s.2

  have hM1 : 1 < M := by omega
  haveI : Fact (1 < M) := ⟨hM1⟩
  have hsmem : ∀ T : E₀.toAffine.Point, T ∈ s.1 ↔ T = P ∨ T = -P := by
    intro T
    rw [hs, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [bot_sup_eq] at hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rcases Int.even_or_odd k with hk | hk
      · left; rw [hk.neg_one_zpow]; simp [ZMod.val_one]
      · right; rw [hk.neg_one_zpow]; exact val_neg_one_smul E₀ hM1 hP
    · rintro (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by simp [ZMod.val_one]⟩
      · refine ⟨-1, ?_, ?_⟩
        · rw [bot_sup_eq]; exact Subgroup.mem_zpowers _
        · exact (val_neg_one_smul E₀ hM1 hP).symm

  let one : {γ : ↥(MulAction.stabilizer (VariableChange K) E₀) //
      ∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (γ : VariableChange K) E₀.toAffine T) T'} :=
    ⟨⟨1, Subgroup.one_mem _⟩, fun T hT => ⟨T, hT, by
      show HEq (Point.vcInvFun (1 : VariableChange K) E₀.toAffine T) T
      exact Point.vcInvFun_one_heq E₀.toAffine T⟩⟩
  let neg : {γ : ↥(MulAction.stabilizer (VariableChange K) E₀) //
      ∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (γ : VariableChange K) E₀.toAffine T) T'} :=
    ⟨⟨negVC E₀, MulAction.mem_stabilizer_iff.mpr (negVC_smul E₀)⟩, fun T hT => ⟨-T, by
      rcases (hsmem T).mp hT with rfl | rfl
      · exact (hsmem _).mpr (Or.inr rfl)
      · rw [neg_neg]; exact (hsmem _).mpr (Or.inl rfl), by
      show HEq (Point.vcInvFun (negVC E₀) E₀.toAffine T) (-T)
      exact Point.vcInvFun_neg_heq_neg E₀ T⟩⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨one, neg, ?_, ?_⟩
  · intro h
    have : ((one.1 : ↥(MulAction.stabilizer (VariableChange K) E₀)) : VariableChange K) = (neg.1 : VariableChange K) := by rw [h]
    exact negVC_ne_one E₀ this.symm
  ·
    rw [Set.eq_univ_iff_forall]
    intro γ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hγ : (γ.1 : VariableChange K) • E₀ = E₀ := MulAction.mem_stabilizer_iff.mp γ.1.2
    obtain ⟨T', hT', hheq⟩ := γ.2 P ((hsmem P).mpr (Or.inl rfl))
    rw [heq_vcInvFun_iff E₀ hγ] at hheq
    by_contra hne
    push_neg at hne
    obtain ⟨hne1, hne2⟩ := hne
    have h1 : (γ.1 : VariableChange K) ≠ 1 := by
      intro h; apply hne1; apply Subtype.ext; apply Subtype.ext; exact h
    have h2 : (γ.1 : VariableChange K) ≠ negVC E₀ := by
      intro h; apply hne2; apply Subtype.ext; apply Subtype.ext; exact h
    rcases (hsmem T').mp hT' with rfl | rfl
    · exact addOrderOf_le_three_of_tr_eq E₀ hγ h1 h2 hheq hP hM
    ·
      have hγ' : (negVC E₀ * (γ.1 : VariableChange K)) • E₀ = E₀ := by rw [mul_smul, hγ, negVC_smul]
      have hfix : tr E₀ (negVC E₀ * (γ.1 : VariableChange K)) hγ' P = P := by
        have := tr_mul E₀ (negVC_smul E₀) hγ P
        rw [hheq, tr_negVC, neg_neg] at this
        convert this using 2
      have h1' : negVC E₀ * (γ.1 : VariableChange K) ≠ 1 := by
        intro h
        apply h2
        have := congrArg (negVC E₀ * ·) h
        simp only [← mul_assoc, negVC_mul_negVC, one_mul, mul_one] at this
        exact this
      have h2' : negVC E₀ * (γ.1 : VariableChange K) ≠ negVC E₀ := by
        intro h
        apply h1
        have := congrArg (negVC E₀ * ·) h
        simp only [← mul_assoc, negVC_mul_negVC, one_mul] at this
        exact this
      exact addOrderOf_le_three_of_tr_eq E₀ hγ' h1' h2' hfix hP hM

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hMK : (M : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (s : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}) :
    Nat.card {γ : ↥(MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) //
        ∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (γ : WeierstrassCurve.VariableChange K) E₀.toAffine T) T'} = 2 :=
  stab2_main K p M hM hMK E₀ s

end S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two (solution)
