-- Prove2me | solution 1 for SingleMachinePrec.Framework.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:21:07.991977+00:00
-- url     : https://prove2.me/submissions/5c1fd3b2-726e-483d-90d0-bf2fe2faf4b4

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

set_option autoImplicit false

namespace C20Aux
open SingleMachinePrec.Framework

/-- No linear extension reverses both endpoints of an edge of `G^S_P`. -/
theorem not_both_rev_rule {N : Type*} {P : N → N → Prop} (L : LinearExtension P)
    (u v : IncPair P) (h : csRule P u v) (hu : L.Reverses u) (hv : L.Reverses v) : False := by
  have hlin := L.isLinearOrder
  have hanti : ∀ a b, L.le a b → L.le b a → a = b := fun a b h1 h2 => hlin.antisymm a b h1 h2
  have htrans : ∀ a b c, L.le a b → L.le b c → L.le a c := fun a b c h1 h2 => hlin.trans a b c h1 h2
  obtain ⟨⟨a, b⟩, hab⟩ := u
  obtain ⟨⟨c, d⟩, hcd⟩ := v
  simp only [LinearExtension.Reverses] at hu hv
  obtain ⟨hba, hne1⟩ := hu
  obtain ⟨hdc, hne2⟩ := hv
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    subst h1; subst h2
    exact hne1 (hanti _ _ hba hdc)
  · simp only at h1 h2
    subst h1
    have had := L.extends_P _ _ h2
    -- b < a ≤ d < b
    have hda : L.le d a := htrans _ _ _ hdc hba
    have : a = d := hanti _ _ had hda
    subst this
    exact hne1 (hanti _ _ hba hdc)
  · simp only at h1 h2
    have had := L.extends_P _ _ h1
    have hcb := L.extends_P _ _ h2
    -- b ≤ a ≤ d ≤ c ≤ b
    have hbd : L.le b d := htrans _ _ _ hba had
    have hbc : L.le b c := htrans _ _ _ hbd hdc
    have hcb' : c = b := hanti _ _ hcb hbc
    subst hcb'
    have hdb : d = c := hanti _ _ hdc hbd
    subst hdb
    have : a = d := hanti _ _ had hba
    exact hne1 this.symm

theorem mem_rounded {N : Type*} [Fintype N] [DecidableEq N] {P : N → N → Prop}
    (x : IncPair P → ℝ) (L : LinearExtension P) (u : IncPair P) :
    u ∈ roundedCover x L ↔ (x u = 1 ∨ (x u = 1 / 2 ∧ ¬ L.Reverses u)) := by
  simp [roundedCover, levelSet, reversedHalf]
  tauto

theorem rev_xor {N : Type*} (S : Instance N) (L : LinearExtension S.P) (u : IncPair S.P) :
    (L.Reverses ⟨(u.1.2, u.1.1), ⟨u.2.2, u.2.1⟩⟩ ↔ ¬ L.Reverses u) := by
  have hlin := L.isLinearOrder
  obtain ⟨⟨a, b⟩, hab⟩ := u
  have hne : a ≠ b := by
    intro h; subst h; exact hab.1 (S.isPartialOrder.refl a)
  simp only [LinearExtension.Reverses]
  constructor
  · rintro ⟨h1, h2⟩ ⟨h3, h4⟩
    exact h2 (hlin.antisymm _ _ h1 h3)
  · intro h
    refine ⟨?_, hne⟩
    rcases hlin.total a b with h1 | h1
    · exact h1
    · exact absurd ⟨h1, fun e => hne e.symm⟩ h

theorem two_k_le {N : Type*} (S : Instance N) (k t : ℕ) (L : Fin t → LinearExtension S.P)
    (hL : IsKFoldRealizer S.P k t L) (u : IncPair S.P) : 2 * k ≤ t := by
  classical
  obtain ⟨_, hk⟩ := hL
  have h1 := hk u
  have h2 := hk ⟨(u.1.2, u.1.1), ⟨u.2.2, u.2.1⟩⟩
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t)))
    (fun i => (L i).Reverses u)
  have heq : (Finset.univ.filter (fun i => (L i).Reverses ⟨(u.1.2, u.1.1), ⟨u.2.2, u.2.1⟩⟩))
      = Finset.univ.filter (fun i => ¬ (L i).Reverses u) := by
    ext i; simp [rev_xor S (L i) u]
  rw [heq] at h2
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  convert (by omega : 2 * k ≤ t)

end C20Aux

open SingleMachinePrec.Framework in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (∀ i, (vertexCoverGraph S.P).IsVertexCover (roundedCover x (L i) : Set (IncPair S.P))) ∧
      (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤ (2 - 2 / ((t : ℝ) / k)) * OPT S := by
  classical
  obtain ⟨hfeas, hopt⟩ := hx
  refine ⟨?_, ?_⟩
  · intro i u v huv
    simp only [Finset.mem_coe, C20Aux.mem_rounded]
    have hs := hfeas.2 u v huv
    rcases hhalf u with hu | hu | hu <;> rcases hhalf v with hv | hv | hv
    all_goals first
      | (exfalso; rw [hu, hv] at hs; norm_num at hs; done)
      | (left; left; exact hu)
      | (right; left; exact hv)
      | skip
    -- remaining: both 1/2
    by_cases hru : (L i).Reverses u
    · by_cases hrv : (L i).Reverses v
      · exfalso
        rcases huv.2 with h | h
        · exact C20Aux.not_both_rev_rule (L i) u v h hru hrv
        · exact C20Aux.not_both_rev_rule (L i) v u h hrv hru
      · right; right; exact ⟨hv, hrv⟩
    · left; right; exact ⟨hu, hru⟩
  · have hOPT : csLPValue S x ≤ OPT S := by
      unfold OPT
      apply Finset.le_inf'
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      have hyf : IsCSLPFeasible S (fun u => if u ∈ C then (1:ℝ) else 0) := by
        refine ⟨fun u => ?_, fun u v huv => ?_⟩
        · by_cases h : u ∈ C <;> simp [h]
        · rcases hC huv with h | h
          · have h' : u ∈ C := h
            by_cases h2 : v ∈ C <;> simp [h', h2]
          · have h' : v ∈ C := h
            by_cases h2 : u ∈ C <;> simp [h', h2]
      have := hopt _ hyf
      have heq : csLPValue S (fun u => if u ∈ C then (1:ℝ) else 0) = weight S C := by
        simp [csLPValue, weight, mul_ite, Finset.sum_ite_mem]
      linarith
    have hsum : ∀ i, weight S (roundedCover x (L i)) =
        ∑ u, if u ∈ roundedCover x (L i) then vertexWeight S u else 0 := by
      intro i; simp [weight, Finset.sum_ite_mem]
    have hcoef : (2 - 2 / ((t : ℝ) / k)) = (1 / (t : ℝ)) * (2 * t - 2 * k) := by
      have ht : (0 : ℝ) < t := by exact_mod_cast hL.1
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; field_simp
      · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        field_simp
    by_cases hne : Nonempty (IncPair S.P)
    · obtain ⟨u0⟩ := hne
      have h2k := C20Aux.two_k_le S k t L hL u0
      have h2kR : (2 * k : ℝ) ≤ t := by exact_mod_cast h2k
      have ht : (0 : ℝ) < t := by exact_mod_cast hL.1
      have hpt : ∀ u, ∑ i, (if u ∈ roundedCover x (L i) then vertexWeight S u else 0) ≤
          (2 * t - 2 * k : ℝ) * (vertexWeight S u * x u) := by
        intro u
        have hvw : 0 ≤ vertexWeight S u := mul_nonneg (S.p_nonneg _) (S.w_nonneg _)
        rcases hhalf u with hu | hu | hu
        · simp [C20Aux.mem_rounded, hu]
        · have hmem : ∀ i, (u ∈ roundedCover x (L i)) ↔ ¬ (L i).Reverses u := by
            intro i; rw [C20Aux.mem_rounded, hu]; norm_num
          simp_rw [hmem]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t)))
            (fun i => (L i).Reverses u)
          simp only [Finset.card_univ, Fintype.card_fin] at hc
          have hk := hL.2 u
          have hcR : ((Finset.univ.filter (fun i => ¬ (L i).Reverses u)).card : ℝ) ≤ t - k := by
            have : (Finset.univ.filter (fun i => ¬ (L i).Reverses u)).card ≤ t - k := by omega
            have h3 : ((Finset.univ.filter (fun i => ¬ (L i).Reverses u)).card : ℝ) ≤ ((t - k : ℕ) : ℝ) := by
              exact_mod_cast this
            have hkt : k ≤ t := by omega
            rw [Nat.cast_sub hkt] at h3
            exact h3
          rw [hu]
          nlinarith
        · have hmem : ∀ i, (u ∈ roundedCover x (L i)) := by
            intro i; rw [C20Aux.mem_rounded, hu]; simp
          simp only [hmem, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hu, mul_one]
          nlinarith
      have hS : ∑ i, weight S (roundedCover x (L i)) ≤ (2 * t - 2 * k : ℝ) * csLPValue S x := by
        simp_rw [hsum]
        rw [Finset.sum_comm, csLPValue, Finset.mul_sum]
        exact Finset.sum_le_sum (fun u _ => hpt u)
      have hcnn : (0 : ℝ) ≤ (1 / (t : ℝ)) * (2 * t - 2 * k) := by
        apply mul_nonneg
        · positivity
        · linarith
      rw [hcoef]
      calc (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i))
          ≤ (1 / (t : ℝ)) * ((2 * t - 2 * k : ℝ) * csLPValue S x) := by
            apply mul_le_mul_of_nonneg_left hS; positivity
        _ = ((1 / (t : ℝ)) * (2 * t - 2 * k)) * csLPValue S x := by ring
        _ ≤ ((1 / (t : ℝ)) * (2 * t - 2 * k)) * OPT S := mul_le_mul_of_nonneg_left hOPT hcnn
    · rw [not_nonempty_iff] at hne
      have hw : ∀ C : Finset (IncPair S.P), weight S C = 0 := by
        intro C; simp [weight, Finset.eq_empty_of_isEmpty C]
      have hO : OPT S = 0 := by
        unfold OPT
        have : weight S = fun _ => 0 := funext hw
        rw [this]
        exact Finset.inf'_const _ _
      simp [hw, hO]
