-- Prove2me | solution 1 for PooledRationing.MaxWeighted.display_57
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:21:40.237714+00:00
-- url     : https://prove2.me/submissions/94fa46da-1271-41d4-9b27-a07db06bd406

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm
import Theorems.Thm_PooledRationing_MaxWeighted_weak_duality

open MeasureTheory ProbabilityTheory Filter Topology

namespace MWDisplay57Aux

open PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem integrable_cost {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (ψ : DetPolicy P c) : Integrable (fun D => f (ψ.toFun D).2) F := by
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hm : Measurable (fun D => f (ψ.toFun D).2) :=
    hfc.measurable.comp (measurable_snd.comp ψ.measurable')
  refine Integrable.of_bound (C := K) hm.aestronglyMeasurable ?_
  filter_upwards [hf] with D hD
  simpa [Real.norm_eq_abs] using hD _ (ψ.mem' D)

theorem integrable_serv {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (R : Fin n → ℝ → ℝ → ℝ) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (ψ : DetPolicy P c) (j : Fin n) :
    Integrable (fun D => R j ((ψ.toFun D).1 j) (D j)) F := by
  have hm : Measurable (fun D => R j ((ψ.toFun D).1 j) (D j)) := by
    have h1 : Measurable (fun D : Fin n → ℝ => ((ψ.toFun D).1 j, D j)) :=
      ((measurable_pi_apply j).comp (measurable_fst.comp ψ.measurable')).prodMk
        (measurable_pi_apply j)
    exact (hRmeas j).comp h1
  refine Integrable.of_bound (C := C) hm.aestronglyMeasurable ?_
  filter_upwards [hDnn] with D hD
  rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg _ _ _)]
  exact hA3R _ _ _ (hPs D hD _ (ψ.mem' D) j)

theorem iter_nonneg {n m : ℕ}
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ) (γ : ℝ)
    (d : ℕ → Fin n → ℝ) (t : ℕ) : 0 ≤ mwsIter sel β R γ d t := by
  cases t with
  | zero => simp [mwsIter]
  | succ t => intro j; simp only [mwsIter]; exact le_max_left _ _

theorem iter_succ {n m : ℕ}
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (sel : (Fin n → ℝ) → DetPolicy P c) (β : Fin n → ℝ) (R : Fin n → ℝ → ℝ → ℝ) (γ : ℝ)
    (d : ℕ → Fin n → ℝ) (t : ℕ) (j : Fin n) :
    mwsIter sel β R γ d (t + 1) j = max 0 (mwsIter sel β R γ d t j +
        γ * (β j - R j (((sel (mwsIter sel β R γ d t)).toFun (d t)).1 j) (d t j))) := rfl

end MWDisplay57Aux

open MWDisplay57Aux PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem solution
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (d : ℕ → Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (T : ℕ) (hT : 1 ≤ T) (γ : ℝ) (hγ : 0 < γ) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, PooledRationing.AsymFeas.detCost F f (sel (mwsIter sel β R γ d t))
        - Gstar F f R β P c
      ≤ 1 / (2 * T * γ) * ∑ t ∈ Finset.range T,
          ((∑ j, (mwsIter sel β R γ d t j) ^ 2) - (∑ j, (mwsIter sel β R γ d (t + 1) j) ^ 2)
            + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t) ∧
    1 / (2 * T * γ) * ∑ t ∈ Finset.range T,
          ((∑ j, (mwsIter sel β R γ d t j) ^ 2) - (∑ j, (mwsIter sel β R γ d (t + 1) j) ^ 2)
            + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t)
      ≤ γ * n * (1 + C) ^ 2 / 2 + γ / 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t := by
  classical
  set w := mwsIter sel β R γ d with hwdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- G at a nonnegative weight equals the Lagrangian of the selected policy
  have hGeq : ∀ v : Fin n → ℝ, 0 ≤ v →
      G F f R β P c v = ∑ j, v j * β j + detCost F f (sel v) - ∑ j, v j * detService F R (sel v) j := by
    intro v hv
    have hg : ∀ D, g P c f R v D = mwsObjective f R v D ((sel v).toFun D) := by
      intro D
      have hl : IsLeast (mwsObjective f R v D '' P c D) (mwsObjective f R v D ((sel v).toFun D)) :=
        ⟨⟨_, (sel v).mem' D, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hsel v hv D hx⟩
      exact hl.csInf_eq
    simp only [G, hg, mwsObjective]
    rw [integral_sub (integrable_cost F f K hf (sel v))
      (integrable_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs (sel v) j).const_mul (v j))]
    rw [integral_finsetSum _ fun j _ =>
        (integrable_serv F R hDnn hRnonneg hRmeas C hA3R hPs (sel v) j).const_mul (v j)]
    simp_rw [integral_const_mul]
    simp only [detCost, detService]
    ring
  have hbdd : BddAbove (G F f R β P c '' {v | 0 ≤ v}) := by
    refine ⟨obj11 F f R β P c, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hGeq v hv]
    exact weak_duality F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg hRmeas B hA3supp
      C hA3R hPs K hf hfeas v hv (sel v) (hsel v hv)
  have hGle : ∀ v : Fin n → ℝ, 0 ≤ v → G F f R β P c v ≤ Gstar F f R β P c := fun v hv =>
    le_csSup hbdd ⟨v, hv, rfl⟩
  -- realized service bounds
  have hRt : ∀ t j, 0 ≤ R j (((sel (w t)).toFun (d t)).1 j) (d t j) ∧
      R j (((sel (w t)).toFun (d t)).1 j) (d t j) ≤ C := fun t j =>
    ⟨hRnonneg _ _ _, hA3R _ _ _ (hPs (d t) (hd t) _ ((sel (w t)).mem' (d t)) j)⟩
  -- one-step inequality
  have hstep : ∀ t, 2 * γ * (detCost F f (sel (w t)) - Gstar F f R β P c) ≤
      (∑ j, (w t j) ^ 2) - (∑ j, (w (t + 1) j) ^ 2)
        + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t := by
    intro t
    set Rr : Fin n → ℝ := fun j => R j (((sel (w t)).toFun (d t)).1 j) (d t j) with hRr
    set ER : Fin n → ℝ := fun j => detService F R (sel (w t)) j with hER
    have hL : (T : ℝ) * γ ^ 2 * Lterm F R β sel γ T d t =
        2 * γ * ∑ j, (w t j * ER j - w t j * Rr j) := by
      simp only [Lterm, hER, hRr, hwdef]
      field_simp
    have hsq : ∀ j, (w (t + 1) j) ^ 2 ≤ (w t j + γ * (β j - Rr j)) ^ 2 := by
      intro j
      rw [hwdef, iter_succ]
      rcases le_total 0 (w t j + γ * (β j - Rr j)) with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h]; simp; positivity
    have hb : ∀ j, (β j - Rr j) ^ 2 ≤ (1 + C) ^ 2 := by
      intro j
      obtain ⟨h0, h1⟩ := hRt t j
      have := hβ j
      simp only [Set.mem_Ioo] at this
      apply sq_le_sq'
      · simp only [hRr]; linarith
      · simp only [hRr]; linarith
    have hsum1 : ∑ j, (w (t + 1) j) ^ 2 ≤ ∑ j, (w t j) ^ 2 + 2 * γ * ∑ j, w t j * (β j - Rr j)
        + γ ^ 2 * ∑ j, (β j - Rr j) ^ 2 := by
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hsq j
      refine this.trans (le_of_eq ?_)
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hsum2 : ∑ j, (β j - Rr j) ^ 2 ≤ n * (1 + C) ^ 2 := by
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hb j
      simpa using this
    have hG := hGle (w t) (iter_nonneg sel β R γ d t)
    rw [hGeq (w t) (iter_nonneg sel β R γ d t)] at hG
    have hsplit : ∑ j, w t j * (β j - Rr j) =
        (∑ j, w t j * β j - ∑ j, w t j * ER j) + ∑ j, (w t j * ER j - w t j * Rr j) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
    have : γ ^ 2 * ∑ j, (β j - Rr j) ^ 2 ≤ γ ^ 2 * (n * (1 + C) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum2 hγ2
    have hER' : ∑ j, w t j * ER j = ∑ j, w t j * detService F R (sel (w t)) j := rfl
    rw [hL]
    nlinarith
  have hsumstep := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => hstep t
  rw [← Finset.mul_sum] at hsumstep
  have htel : ∑ t ∈ Finset.range T, ((∑ j, (w t j) ^ 2) - (∑ j, (w (t + 1) j) ^ 2)) =
      (∑ j, (w 0 j) ^ 2) - ∑ j, (w T j) ^ 2 := by
    rw [Finset.sum_range_sub']
  have hw0 : ∑ j, (w 0 j) ^ 2 = 0 := by simp [hwdef, mwsIter]
  have hwT : 0 ≤ ∑ j, (w T j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumstep
    have h2Tγ : 0 < 2 * (T : ℝ) * γ := by positivity
    rw [show (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, detCost F f (sel (w t)) - Gstar F f R β P c
        = 1 / (2 * T * γ) * (2 * γ * (∑ t ∈ Finset.range T, detCost F f (sel (w t))
            - T * Gstar F f R β P c)) by field_simp]
    exact mul_le_mul_of_nonneg_left hsumstep (by positivity)
  · have hsplit : ∑ t ∈ Finset.range T,
        ((∑ j, (w t j) ^ 2) - (∑ j, (w (t + 1) j) ^ 2)
          + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t) =
        (∑ t ∈ Finset.range T, ((∑ j, (w t j) ^ 2) - (∑ j, (w (t + 1) j) ^ 2)))
          + T * (γ ^ 2 * n * (1 + C) ^ 2)
          + T * γ ^ 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t := by
      rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
    rw [hsplit, htel, hw0]
    rw [show γ * n * (1 + C) ^ 2 / 2 + γ / 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t =
        1 / (2 * T * γ) * (T * (γ ^ 2 * n * (1 + C) ^ 2)
          + T * γ ^ 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t) by field_simp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
