-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:44.573715+00:00
-- url     : https://prove2.me/submissions/cbe7927d-4a2d-48fb-9b56-5c0fc7146c78

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_mem_kSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {P U : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]
    [AddCommGroup U] [Module ℂ U] (ε : Fin n → Bool) (G : Fin n → Fin n → Module.End ℂ P)
    (F : Fin n → Fin n → Module.End ℂ U) (μ : Fin n → ℝ) (x : P) (hR : KRel ε G) (hU : KUnit ε G)
    (hx : KHighest ε G μ x) (p : P →ₗ[ℂ] U) (hp : ∀ a b, ε a = ε b → ∀ y, p (G a b y) = F a b (p y))
    (hpx : p x ≠ 0) (hT : kSpan ε F (p x) = ⊤) : Function.Bijective (p.domRestrict (kSpan ε G x)) := by

  obtain ⟨B, hBdef⟩ : ∃ B : Submodule ℂ P, B = sInf {S : Submodule ℂ P | x ∈ S ∧
      ∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S} := ⟨_, rfl⟩
  have hxB : x ∈ B := by
    rw [hBdef, Submodule.mem_sInf]; exact fun S hS => hS.1
  have hlow : ∀ a b, b < a → ε a = ε b → ∀ y ∈ B, G a b y ∈ B := by
    intro a b hba hab y hy
    rw [hBdef, Submodule.mem_sInf] at hy ⊢
    exact fun S hS => hS.2 a b hba hab y (hy S hS)
  have hBle : ∀ S : Submodule ℂ P, x ∈ S →
      (∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S) → B ≤ S := by
    intro S hxS hS
    rw [hBdef]; exact sInf_le ⟨hxS, hS⟩

  have hBst : KStable ε G B := by
    have key : B ≤ B ⊓ ⨅ c : Fin n, ⨅ d : Fin n, ⨅ (_ : ε c = ε d), B.comap (G c d) := by
      refine hBle _ ?_ ?_
      · refine Submodule.mem_inf.2 ⟨hxB, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro c d hcd
        rcases lt_trichotomy c d with hlt | heq | hgt
        · rw [hx.2 c d hlt hcd]; exact B.zero_mem
        · subst heq; rw [hx.1 c]; exact B.smul_mem _ hxB
        · exact hlow c d hgt hcd x hxB
      · intro a b hba hab y hy
        rw [Submodule.mem_inf] at hy ⊢
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
        refine ⟨hlow a b hba hab y hy.1, fun c d hcd => ?_⟩
        have hcomm : G c d (G a b y) - G a b (G c d y) =
            (if d = a then G c b else 0) y - (if b = c then G a d else 0) y :=
          LinearMap.congr_fun (hR c d a b hcd hab) y
        have he : G c d (G a b y) = G a b (G c d y) +
            ((if d = a then G c b else 0) y - (if b = c then G a d else 0) y) := by
          rw [← hcomm]; abel
        rw [he]
        refine B.add_mem (hlow a b hba hab _ (hy.2 c d hcd)) (B.sub_mem ?_ ?_)
        · split_ifs with h
          · subst h; exact hy.2 c b (hcd.trans hab)
          · simpa using B.zero_mem
        · split_ifs with h
          · subst h; exact hy.2 a d (hab.trans hcd)
          · simpa using B.zero_mem
    intro a b hab y hy
    have hy' := key hy
    rw [Submodule.mem_inf] at hy'
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy'
    exact hy'.2 a b hab
  have hMB : kSpan ε G x ≤ B := uq_kSpan_le ε G hxB hBst
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ P, N = LinearMap.ker p ⊓ kSpan ε G x := ⟨_, rfl⟩
    have hNst : KStable ε G N := by
      intro a b hab z hz
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hz ⊢
      exact ⟨by rw [hp a b hab z, hz.1, map_zero], uq_kSpan_stable ε G x a b hab z hz.2⟩
    have hNo : KStable ε G Nᗮ := by
      intro a b hab m hm
      rw [Submodule.mem_orthogonal] at hm ⊢
      intro u hu
      rw [← hU b a hab.symm u m]
      exact hm _ (hNst b a hab.symm u hu)
    have hzero : ∀ v, v ∈ N → v ∈ Nᗮ → v = 0 := fun v h1 h2 =>
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 v h1)
    obtain ⟨nn, hnn, mm, hmm, hxnm⟩ : ∃ y ∈ N, ∃ z ∈ Nᗮ, x = y + z := by
      first
        | exact N.exists_add_mem_mem_orthogonal x
        | (obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1
              (show x ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_completeSpace]; exact Submodule.mem_top)
           exact ⟨y, hy, z, hz, e.symm⟩)
    have hnr : ∀ c d, c < d → ε c = ε d → G c d nn = 0 := by
      intro c d hcd hε
      have h0 : G c d nn + G c d mm = 0 := by rw [← map_add, ← hxnm, hx.2 c d hcd hε]
      have h1 : G c d nn = -G c d mm := eq_neg_of_add_eq_zero_left h0
      refine hzero _ (hNst c d hε nn hnn) ?_
      rw [h1]; exact Nᗮ.neg_mem (hNo c d hε mm hmm)
    have hnB : nn ∈ B := hMB (Submodule.mem_inf.1 (hNdef ▸ hnn)).2
    have hmB : mm ∈ B := by
      have hme : mm = x - nn := by rw [hxnm]; abel
      rw [hme]; exact B.sub_mem hxB hnB
    have hS : ∀ y ∈ B, ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ := by
      let S : Submodule ℂ P :=
        { carrier := {y | ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ}
          add_mem' := by
            intro y z hy hz
            simp only [Set.mem_setOf_eq, inner_add_right] at hy hz ⊢
            rw [add_mul, mul_add, hy, hz]
          zero_mem' := by simp
          smul_mem' := by
            intro c y hy
            simp only [Set.mem_setOf_eq, inner_smul_right] at hy ⊢
            rw [mul_assoc, hy]; ring }
      have hBS : B ≤ S := by
        refine hBle S ?_ ?_
        · show ⟪nn, x⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, x⟫_ℂ
          rw [inner_self_eq_norm_sq_to_K]
          first | rfl | simp | norm_cast
        · intro a b hba hab y _
          show ⟪nn, G a b y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, G a b y⟫_ℂ
          rw [← hU b a hab.symm nn y, ← hU b a hab.symm x y, hnr b a hba hab.symm,
            hx.2 b a hba hab.symm]
          simp
      exact fun y hy => hBS hy
    have key := hS mm hmB
    have hnm : ⟪nn, mm⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hmm nn hnn
    have hnx : ⟪nn, x⟫_ℂ = ⟪nn, nn⟫_ℂ := by rw [hxnm, inner_add_right, hnm, add_zero]
    have hxm : ⟪x, mm⟫_ℂ = ⟪mm, mm⟫_ℂ := by rw [hxnm, inner_add_left, hnm, zero_add]
    rw [hnm, hnx, hxm, zero_mul] at key
    have hn0 : nn = 0 := by
      rcases mul_eq_zero.1 key.symm with h | h
      · exact inner_self_eq_zero.1 h
      · exfalso
        have hm0 : mm = 0 := inner_self_eq_zero.1 h
        have hxN : x ∈ N := by rw [hxnm, hm0, add_zero]; exact hnn
        rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hxN
        exact hpx hxN.1
    have hxo : x ∈ Nᗮ := by rw [hxnm, hn0, zero_add]; exact hmm
    have hMo : kSpan ε G x ≤ Nᗮ := uq_kSpan_le ε G hxo hNo
    intro z₁ z₂ hz
    have hd : (z₁ : P) - z₂ ∈ N := by
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨?_, Submodule.sub_mem _ z₁.2 z₂.2⟩
      rw [map_sub, sub_eq_zero]; simpa using hz
    have h3 := hzero _ hd (hMo (Submodule.sub_mem _ z₁.2 z₂.2))
    exact Subtype.ext (sub_eq_zero.1 h3)
  · intro u
    have hT' : kSpan ε F (p x) ≤ (kSpan ε G x).map p := by
      refine uq_kSpan_le ε F (Submodule.mem_map_of_mem (uq_mem_kSpan ε G x)) ?_
      intro a b hab v hv
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
      rw [← hp a b hab z]
      exact Submodule.mem_map_of_mem (uq_kSpan_stable ε G x a b hab z hz)
    rw [hT] at hT'
    obtain ⟨z, hz, hzu⟩ := Submodule.mem_map.1 (hT' Submodule.mem_top)
    exact ⟨⟨z, hz⟩, by simpa using hzu⟩
end ReciprocityTheory.ChartRestriction.DS.HW
