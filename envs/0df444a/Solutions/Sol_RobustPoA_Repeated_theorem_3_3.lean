-- Prove2me | solution 1 for RobustPoA.Repeated.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:21:46.918382+00:00
-- url     : https://prove2.me/submissions/12c6fe45-48db-414c-be6a-c627a7825e65

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

namespace RRAux_RobustPoA_Repeated_theorem_3_3

open RobustPoA.Static RobustPoA.Repeated

-- core inequality: (1 - μ) A ≤ λ c + E
theorem key {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hs : IsSmooth C lam mu)
    (seq : ℕ → ∀ i, S i) (ε : ι → ℕ → ℝ)
    (hε : ∀ i, ∀ T : ℕ, 1 ≤ T → ∀ t' : S i,
      (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, C i (seq t) ≤
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          C i (Function.update (seq t) i t') + ε i T)
    (s' : ∀ i, S i) (T : ℕ) (hT : 1 ≤ T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, cost C (seq t) ≤
      lam * cost C s' + mu * ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, cost C (seq t))
        + ∑ i, ε i T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, cost C (seq t)
      = ∑ i, (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, C i (seq t) := by
    unfold cost
    rw [Finset.sum_comm, Finset.mul_sum]
  have h2 : ∑ i, (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, C i (seq t) ≤
      ∑ i, ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          C i (Function.update (seq t) i (s' i)) + ε i T) :=
    Finset.sum_le_sum (fun i _ => hε i T hT (s' i))
  have h3 : ∑ i, ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          C i (Function.update (seq t) i (s' i)) + ε i T)
      = (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ∑ i, C i (Function.update (seq t) i (s' i))
        + ∑ i, ε i T := by
    rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.mul_sum]
  have h4 : ∑ t ∈ Finset.Icc 1 T, ∑ i, C i (Function.update (seq t) i (s' i)) ≤
      ∑ t ∈ Finset.Icc 1 T, (lam * cost C s' + mu * cost C (seq t)) :=
    Finset.sum_le_sum (fun t _ => hs (seq t) s')
  have h5 : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (lam * cost C s' + mu * cost C (seq t))
      = lam * cost C s' + mu * ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, cost C (seq t)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum]
    simp only [nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
  have h6 := mul_le_mul_of_nonneg_left h4 (le_of_lt (one_div_pos.mpr hTpos))
  rw [h5] at h6
  linarith

theorem smooth_ge_one {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hmu : mu < 1) (hs : IsSmooth C lam mu)
    (s' : ∀ i, S i) (hpos : 0 < cost C s') : 1 ≤ lam / (1 - mu) := by
  have h := hs s' s'
  simp only [Function.update_eq_self] at h
  have h' : cost C s' ≤ lam * cost C s' + mu * cost C s' := h
  have h1 : 1 - mu ≤ lam := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem div_bound (A c lam mu E : ℝ) (hmu : mu < 1) (hc : 0 < c)
    (h : A ≤ lam * c + mu * A + E) :
    A / c ≤ lam / (1 - mu) + E / ((1 - mu) * c) := by
  have h1 : 0 < 1 - mu := by linarith
  rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt (mul_pos h1 hc)),
    div_le_div_iff₀ hc (mul_pos h1 (mul_pos h1 hc))]
  have : A * (1 - mu) ≤ lam * c + E := by linarith
  have h2 : 0 < (1 - mu) * c := mul_pos h1 hc
  nlinarith

end RRAux_RobustPoA_Repeated_theorem_3_3

open RobustPoA.Repeated in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ)
    (hC : ∀ s, 0 ≤ RobustPoA.Static.cost C s)
    (hsmooth : ∃ lam mu : ℝ, mu < 1 ∧ RobustPoA.Static.IsSmooth C lam mu)
    (seq : ℕ → ∀ i, S i) (hreg : VanishingRegret C seq)
    (s' : ∀ i, S i) (hpos : 0 < RobustPoA.Static.cost C s') :
    ∃ η : ℕ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) ∧
      ∀ T : ℕ, 1 ≤ T →
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
          (RobustPoA.Static.robustPoA C + η T) * RobustPoA.Static.cost C s' := by
  classical
  choose ε hε0 hε using hreg
  obtain ⟨l0, m0, hm0, hs0⟩ := hsmooth
  have hle : RobustPoA.Static.robustPoA C ≤ ((l0 / (1 - m0) : ℝ) : EReal) :=
    sInf_le ⟨l0, m0, hm0, hs0, rfl⟩
  have hge : ((1 : ℝ) : EReal) ≤ RobustPoA.Static.robustPoA C := by
    apply le_sInf
    rintro r ⟨l, m, hm, hs, rfl⟩
    exact EReal.coe_le_coe_iff.mpr
      (RRAux_RobustPoA_Repeated_theorem_3_3.smooth_ge_one C l m hm hs s' hpos)
  have hne_top : RobustPoA.Static.robustPoA C ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  have hne_bot : RobustPoA.Static.robustPoA C ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
  set ρ := (RobustPoA.Static.robustPoA C).toReal with hρdef
  have hρ : RobustPoA.Static.robustPoA C = (ρ : EReal) :=
    (EReal.coe_toReal hne_top hne_bot).symm
  have happrox : ∀ δ : ℝ, 0 < δ → ∃ l m : ℝ, m < 1 ∧ RobustPoA.Static.IsSmooth C l m ∧
      l / (1 - m) < ρ + δ := by
    intro δ hδ
    by_contra hcon
    push Not at hcon
    have : ((ρ + δ : ℝ) : EReal) ≤ RobustPoA.Static.robustPoA C := by
      apply le_sInf
      rintro r ⟨l, m, hm, hs, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hcon l m hm hs)
    rw [hρ, EReal.coe_le_coe_iff] at this
    linarith
  set c := RobustPoA.Static.cost C s' with hcdef
  refine ⟨fun T => max (((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
      RobustPoA.Static.cost C (seq t)) / c - ρ) 0, ?_, ?_⟩
  · rw [tendsto_order]
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun T => lt_of_lt_of_le ha (le_max_right _ _))
    · intro b hb
      obtain ⟨l, m, hm, hs, hlm⟩ := happrox (b / 2) (by linarith)
      have hE : Filter.Tendsto (fun T => ∑ i, ε i T) Filter.atTop (nhds 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hε0 i)
        simpa using this
      have hE2 : Filter.Tendsto (fun T => (∑ i, ε i T) / ((1 - m) * c))
          Filter.atTop (nhds 0) := by
        simpa using hE.div_const ((1 - m) * c)
      have hev := (tendsto_order.1 hE2).2 (b / 2) (by linarith)
      filter_upwards [hev, Filter.eventually_ge_atTop 1] with T hT1 hT2
      apply max_lt _ hb
      have hk := RRAux_RobustPoA_Repeated_theorem_3_3.key C l m hs seq ε hε s' T hT2
      have hd := RRAux_RobustPoA_Repeated_theorem_3_3.div_bound _ c l m _ hm hpos hk
      linarith
  · intro T hT
    have hL : (1 / ((T : ℝ) : EReal)) * ((∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) : ℝ) : EReal)
        = (((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) : ℝ) : EReal) := by
      rw [EReal.coe_mul, EReal.coe_div]; simp
    simp only [] ; rw [hL, hρ, ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have h1 := le_max_left (((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
      RobustPoA.Static.cost C (seq t)) / c - ρ) 0
    have h2 : ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t)) / c ≤
        ρ + max (((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          RobustPoA.Static.cost C (seq t)) / c - ρ) 0 := by linarith
    rwa [div_le_iff₀ hpos] at h2

#print axioms solution
