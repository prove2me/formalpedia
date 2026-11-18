-- Prove2me | solution 1 for WeldedPath.single_cycle_coupling
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T18:04:28.405196+00:00
-- url     : https://prove2.me/submissions/0b5675ec-a8f9-48b7-b8d9-19522bc6bacd

import Theorems.Thm_WeldedPath_single_cycle_switching_chain
import Definitions.Def_WeldedPath_successProb
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

set_option autoImplicit false

-- Solutions.QueryHybridWeights
section

namespace QAlgorithms.QueryHybrid

open scoped BigOperators

section Weights

variable {α β Z : Type*} [Fintype α] [Fintype β] [Fintype Z]

theorem weighted_disagreement_le (w : β → ℝ) (s : Z → ℝ)
    (P : β → Z → Prop) [∀ b, DecidablePred (P b)] (δ : ℝ)
    (hs : ∀ z, 0 ≤ s z)
    (hP : ∀ z, (∑ b, if P b z then w b else 0) ≤ δ) :
    (∑ b, w b * ∑ z, if P b z then s z else 0) ≤ δ * ∑ z, s z := by
  calc
    _ = ∑ z, (∑ b, if P b z then w b else 0) * s z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ ≤ ∑ z, δ * s z := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hP z) (hs z))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem coupling_sum_left (w : α → β → ℝ) (μ : α → ℝ)
    (hrow : ∀ a, ∑ b, w a b = μ a) (f : α → ℝ) :
    (∑ a, μ a * f a) = ∑ a, ∑ b, w a b * f a := by
  simp only [← hrow, Finset.sum_mul]

theorem coupling_sum_right (w : α → β → ℝ) (ν : β → ℝ)
    (hcol : ∀ b, ∑ a, w a b = ν b) (f : β → ℝ) :
    (∑ b, ν b * f b) = ∑ a, ∑ b, w a b * f b := by
  rw [Finset.sum_comm]
  simp only [← hcol, Finset.sum_mul]

end Weights

section Uniform

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def uniformWeight (S : Finset α) (a : α) : ℝ :=
  if a ∈ S then 1 / (S.card : ℝ) else 0

theorem uniformWeight_nonneg (S : Finset α) (a : α) : 0 ≤ uniformWeight S a := by
  unfold uniformWeight
  split_ifs <;> positivity

theorem uniformWeight_sum (S : Finset α) (f : α → ℝ) :
    (∑ a, uniformWeight S a * f a) = WeldedPath.avgOver S f := by
  simp only [uniformWeight, ite_mul, zero_mul, one_div, WeldedPath.avgOver]
  rw [Finset.sum_ite_mem, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm, Finset.univ_inter]

theorem uniformWeight_total (S : Finset α) (hS : S.Nonempty) :
    (∑ a, uniformWeight S a) = 1 := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simpa [WeldedPath.avgOver, hc] using uniformWeight_sum S (fun _ => (1 : ℝ))

end Uniform

end QAlgorithms.QueryHybrid

end


-- Solutions.WeldedPathCouplingLift
section

namespace WeldedPath.CouplingLift

open Classical QAlgorithms QAlgorithms.QueryHybrid
open scoped BigOperators

noncomputable def labelSupport (n : ℕ) : Finset (Equiv.Perm (Label n)) :=
  Finset.univ.filter fun τ => τ 0 = 0

noncomputable def edgeProdSupport {n : ℕ} (l : ℕ) (G : WeldedInstance n) :
    Finset (Equiv.Perm G.edges) :=
  Finset.univ.filter (G.IsEdgePerm l)

noncomputable def edgeSingSupport {n : ℕ} (l : ℕ) (G : WeldedInstance n) :
    Finset (Equiv.Perm G.edges) :=
  (edgeProdSupport l G).filter G.SingleCycle

theorem prodSupport_eq {n : ℕ} (l : ℕ) (G : WeldedInstance n) :
    G.prodSupport l = labelSupport n ×ˢ edgeProdSupport l G := by
  classical
  ext σ
  simp [WeldedInstance.prodSupport, labelSupport, edgeProdSupport]

theorem singSupport_eq {n : ℕ} (l : ℕ) (G : WeldedInstance n) :
    G.singSupport l = labelSupport n ×ˢ edgeSingSupport l G := by
  classical
  ext σ
  simp [WeldedInstance.singSupport, WeldedInstance.prodSupport, labelSupport,
    edgeProdSupport, edgeSingSupport, and_assoc]

theorem labelSupport_nonempty (n : ℕ) : (labelSupport n).Nonempty := by
  classical
  exact ⟨Equiv.refl _, by simp [labelSupport]⟩

theorem uniformWeight_product {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Finset α) (T : Finset β) (a : α) (b : β) :
    uniformWeight (S ×ˢ T) (a, b) = uniformWeight S a * uniformWeight T b := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ T <;>
    simp [uniformWeight, ha, hb, Finset.card_product, one_div, mul_inv_rev, mul_comm]

theorem disagreement_sum_mono {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → β) (b : β) (g : α → γ) (c : γ)
    (h : ∀ a, f a = b → g a = c) :
    (∑ a, if g a ≠ c then w a else 0) ≤ ∑ a, if f a ≠ b then w a else 0 := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases hf : f a = b
  · simp [hf, h a hf]
  · by_cases hg : g a = c <;> simp [hf, hg, hw a]

theorem Nb_disagreement_bound {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (π : Equiv.Perm G.edges) (w : Equiv.Perm G.edges → ℝ) (d : ℝ)
    (hd : 0 ≤ d) (hw : ∀ ρ, 0 ≤ w ρ)
    (hf : ∀ e, (∑ ρ, if ρ e ≠ π e then w ρ else 0) ≤ d)
    (hi : ∀ e, (∑ ρ, if ρ.symm e ≠ π.symm e then w ρ else 0) ≤ d)
    (v : ℕ) (α : Fin 3) :
    (∑ ρ, if G.Nb l ρ v α ≠ G.Nb l π v α then w ρ else 0) ≤ d := by
  classical
  by_cases hv : IsVertex n v
  · cases hα : G.eAlpha v α with
    | none => simpa [WeldedInstance.Nb, hv, hα] using hd
    | some e =>
      by_cases he : e ∈ G.edges
      · by_cases hb : G.bEdge l e = none
        · simpa [WeldedInstance.Nb, hv, hα, he, hb] using hd
        · by_cases ht : v = e.tail
          · subst v
            have hm := disagreement_sum_mono w hw (fun ρ => ρ ⟨e, he⟩) (π ⟨e, he⟩)
              (fun ρ => (ρ ⟨e, he⟩).1.head n) ((π ⟨e, he⟩).1.head n)
              (fun ρ h => congrArg (fun a : G.edges => a.1.head n) h)
            simpa [WeldedInstance.Nb, hv, hα, he, hb] using hm.trans (hf ⟨e, he⟩)
          · by_cases hh : v = e.head n
            · subst v
              have hm := disagreement_sum_mono w hw (fun ρ => ρ.symm ⟨e, he⟩)
                (π.symm ⟨e, he⟩) (fun ρ => (ρ.symm ⟨e, he⟩).1.tail)
                (π.symm ⟨e, he⟩).1.tail
                (fun ρ h => congrArg (fun a : G.edges => a.1.tail) h)
              simpa [WeldedInstance.Nb, hv, hα, he, hb, ht] using hm.trans (hi ⟨e, he⟩)
            · simpa [WeldedInstance.Nb, hv, hα, he, hb, ht, hh] using hd
      · simpa [WeldedInstance.Nb, hv, hα, he] using hd
  · simpa [WeldedInstance.Nb, hv] using hd

theorem oracle_disagreement_bound {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (τ : Equiv.Perm (Label n)) (π : Equiv.Perm G.edges)
    (w : Equiv.Perm G.edges → ℝ) (d : ℝ) (hd : 0 ≤ d) (hw : ∀ ρ, 0 ≤ w ρ)
    (hf : ∀ e, (∑ ρ, if ρ e ≠ π e then w ρ else 0) ≤ d)
    (hi : ∀ e, (∑ ρ, if ρ.symm e ≠ π.symm e then w ρ else 0) ≤ d)
    (x : Qubits (2 * n + 1) × Fin 3) :
    (∑ ρ, if G.oracleFn l (τ, ρ) x ≠ G.oracleFn l (τ, π) x then w ρ else 0) ≤ d := by
  classical
  by_cases hx : bitsToNat x.1 < labelBound n + 1
  · let v : ℕ := (τ.symm ⟨bitsToNat x.1, hx⟩).1
    have hm := disagreement_sum_mono w hw (fun ρ => G.Nb l ρ v x.2)
      (G.Nb l π v x.2) (fun ρ => G.oracleFn l (τ, ρ) x) (G.oracleFn l (τ, π) x)
      (by
        intro ρ h
        simp only [WeldedInstance.oracleFn, dif_pos hx, WeldedInstance.F]
        change natToBits (2 * n + 1)
          (if h' : G.Nb l ρ v x.2 < labelBound n + 1 then τ ⟨_, h'⟩ else ⟨_, hx⟩).val = _
        simp only [h]
        rfl)
    exact hm.trans (Nb_disagreement_bound l G π w d hd hw hf hi v x.2)
  · simpa [WeldedInstance.oracleFn, hx] using hd

noncomputable def liftWeight {n : ℕ} (G : WeldedInstance n)
    (w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ)
    (σh σg : Equiv.Perm (Label n) × Equiv.Perm G.edges) : ℝ :=
  if σg.1 = σh.1 then uniformWeight (labelSupport n) σh.1 * w σh.2 σg.2 else 0

theorem liftWeight_nonneg {n : ℕ} (G : WeldedInstance n)
    (w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ) (hw : ∀ π ρ, 0 ≤ w π ρ)
    (σh σg : Equiv.Perm (Label n) × Equiv.Perm G.edges) : 0 ≤ liftWeight G w σh σg := by
  classical
  unfold liftWeight
  split_ifs
  · exact mul_nonneg (uniformWeight_nonneg _ _) (hw _ _)
  · exact le_rfl

theorem liftWeight_row {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ)
    (hrow : ∀ π, ∑ ρ, w π ρ = uniformWeight (edgeSingSupport l G) π)
    (σh : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    (∑ σg, liftWeight G w σh σg) = uniformWeight (G.singSupport l) σh := by
  classical
  rcases σh with ⟨τ, π⟩
  rw [singSupport_eq, uniformWeight_product, Fintype.sum_prod_type]
  calc
    _ = ∑ ρ, liftWeight G w (τ, π) (τ, ρ) := by
      apply Finset.sum_eq_single τ
      · intro τ' _ hτ
        simp [liftWeight, hτ]
      · simp
    _ = _ := by simp only [liftWeight, ↓reduceIte, ← Finset.mul_sum, hrow]

theorem liftWeight_col {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ)
    (hcol : ∀ ρ, ∑ π, w π ρ = uniformWeight (edgeProdSupport l G) ρ)
    (σg : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    (∑ σh, liftWeight G w σh σg) = uniformWeight (G.prodSupport l) σg := by
  classical
  rcases σg with ⟨τ, ρ⟩
  rw [prodSupport_eq, uniformWeight_product, Fintype.sum_prod_type]
  calc
    _ = ∑ π, liftWeight G w (τ, π) (τ, ρ) := by
      apply Finset.sum_eq_single τ
      · intro τ' _ hτ
        simp [liftWeight, Ne.symm hτ]
      · simp
    _ = _ := by simp only [liftWeight, ↓reduceIte, ← Finset.mul_sum, hcol]

theorem liftWeight_disagreement {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hw : ∀ π ρ, 0 ≤ w π ρ)
    (hf : ∀ π e, (∑ ρ, if ρ e ≠ π e then w π ρ else 0) ≤
      δ * uniformWeight (edgeSingSupport l G) π)
    (hi : ∀ π e, (∑ ρ, if ρ.symm e ≠ π.symm e then w π ρ else 0) ≤
      δ * uniformWeight (edgeSingSupport l G) π)
    (σh : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (x : Qubits (2 * n + 1) × Fin 3) :
    (∑ σg, if G.oracleFn l σg x ≠ G.oracleFn l σh x then liftWeight G w σh σg else 0) ≤
      δ * uniformWeight (G.singSupport l) σh := by
  classical
  rcases σh with ⟨τ, π⟩
  rw [singSupport_eq, uniformWeight_product, Fintype.sum_prod_type]
  calc
    _ = ∑ ρ, if G.oracleFn l (τ, ρ) x ≠ G.oracleFn l (τ, π) x then
          liftWeight G w (τ, π) (τ, ρ) else 0 := by
      apply Finset.sum_eq_single τ
      · intro τ' _ hτ
        simp [liftWeight, hτ]
      · simp
    _ = uniformWeight (labelSupport n) τ *
        (∑ ρ, if G.oracleFn l (τ, ρ) x ≠ G.oracleFn l (τ, π) x then w π ρ else 0) := by
      simp only [liftWeight, ↓reduceIte, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ uniformWeight (labelSupport n) τ *
        (δ * uniformWeight (edgeSingSupport l G) π) := by
      apply mul_le_mul_of_nonneg_left _ (uniformWeight_nonneg _ _)
      exact oracle_disagreement_bound l G τ π (w π) _
        (mul_nonneg hδ (uniformWeight_nonneg _ _)) (hw π) (hf π) (hi π) x
    _ = _ := by ring

end WeldedPath.CouplingLift

end


-- Solutions.CouplingHarmonic
section

namespace WeldedPath.CouplingHarmonic

theorem reciprocal_sum_eq_harmonic (m : ℕ) :
    (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) = (harmonic m : ℝ) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, one_div]

theorem reciprocal_sum_le (n m : ℕ) (hm : 1 ≤ m) (hhi : m ≤ 2 ^ n) :
    (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤ (n : ℝ) + 1 := by
  rw [reciprocal_sum_eq_harmonic]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpow : (m : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hhi
  have hlog : Real.log (m : ℝ) ≤ (n : ℝ) := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hmpos hpow
      _ = (n : ℝ) * Real.log 2 := Real.log_pow 2 n
      _ ≤ (n : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      _ = (n : ℝ) := mul_one _
  have hh := harmonic_le_one_add_log m
  linarith

theorem harmonic_error_le (n m : ℕ) (hn : 1 ≤ n)
    (hlo : 2 ^ (n - 1) ≤ m) (hhi : m ≤ 2 ^ n) :
    (2 / (m : ℝ)) * (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤
      8 * (n : ℝ) / (2 : ℝ) ^ n := by
  have hm : 1 ≤ m := (Nat.one_le_pow (n - 1) 2 (by omega)).trans hlo
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hN : (2 : ℝ) ^ n ≤ 2 * (m : ℝ) := by
    have hn' : n = (n - 1) + 1 := by omega
    have hlo' : (2 : ℝ) ^ (n - 1) ≤ (m : ℝ) := by exact_mod_cast hlo
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by rw [← pow_succ, ← hn']
      _ ≤ (m : ℝ) * 2 := mul_le_mul_of_nonneg_right hlo' (by norm_num)
      _ = 2 * (m : ℝ) := mul_comm _ _
  have hrecip : 2 / (m : ℝ) ≤ 4 / (2 : ℝ) ^ n := by
    apply (div_le_div_iff₀ hmpos hNpos).mpr
    linarith
  have hsum : (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤ 2 * (n : ℝ) := by
    have hh := reciprocal_sum_le n m hm hhi
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    _ ≤ (2 / (m : ℝ)) * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (4 / (2 : ℝ) ^ n) * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hrecip (by positivity)
    _ = _ := by ring

theorem dyadic_certificate_sum_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin (2 ^ n), 4 / ((2 : ℝ) ^ n * ((i : ℝ) + 1))) ≤
      16 * (n : ℝ) / (2 : ℝ) ^ n := by
  have hlo : (2 : ℕ) ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
  have hh := harmonic_error_le n (2 ^ n) hn hlo le_rfl
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hh
  calc
    _ = ∑ r ∈ Finset.range (2 ^ n), 4 / ((2 : ℝ) ^ n * ((r : ℝ) + 1)) :=
      (Finset.sum_range _).symm
    _ = 2 * ((2 / (2 : ℝ) ^ n) *
        (∑ r ∈ Finset.range (2 ^ n), 1 / ((r : ℝ) + 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [div_mul_eq_div_div]
      ring
    _ ≤ 2 * (8 * (n : ℝ) / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

theorem truncated_harmonic_error_le (n m : ℕ) (hn : 1 ≤ n)
    (hlo : 2 ^ (n - 1) ≤ m) (hhi : m ≤ 2 ^ n) :
    (2 / (m : ℝ)) * (∑ r ∈ Finset.Icc 2 m, 1 / (r : ℝ)) ≤
      8 * (n : ℝ) / (2 : ℝ) ^ n := by
  apply le_trans _ (harmonic_error_le n m hn hlo hhi)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [reciprocal_sum_eq_harmonic]
  have hsum : (∑ r ∈ Finset.Icc 2 m, 1 / (r : ℝ)) ≤
      ∑ r ∈ Finset.Icc 1 m, 1 / (r : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc (by omega) le_rfl
    · intro r _ _; positivity
  exact hsum.trans_eq (by simp [harmonic_eq_sum_Icc, Rat.cast_sum, one_div])

theorem small_n_error_ge_one (n cutoff : ℕ) (hn : 1 ≤ n) (hsmall : n ≤ cutoff) :
    1 ≤ (2 : ℝ) ^ cutoff * (n : ℝ) / (2 : ℝ) ^ n := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ cutoff := by gcongr; norm_num
  calc
    1 * (2 : ℝ) ^ n = (2 : ℝ) ^ n := one_mul _
    _ ≤ (2 : ℝ) ^ cutoff := hp
    _ ≤ (2 : ℝ) ^ cutoff * (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hn'
        (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) cutoff))

section Independent

variable {α β X : Type*} [Fintype α] [Fintype β]

theorem product_row (μ : α → ℝ) (ν : β → ℝ) (hν : ∑ b, ν b = 1) (a : α) :
    (∑ b, μ a * ν b) = μ a := by rw [← Finset.mul_sum, hν, mul_one]

theorem product_col (μ : α → ℝ) (ν : β → ℝ) (hμ : ∑ a, μ a = 1) (b : β) :
    (∑ a, μ a * ν b) = ν b := by rw [← Finset.sum_mul, hμ, one_mul]

theorem product_disagreement_le (μ : α → ℝ) (ν : β → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (htotal : ∑ b, ν b = 1)
    (P : α → β → X → Prop) [∀ a b, DecidablePred (P a b)] (a : α) (x : X) :
    (∑ b, if P a b x then μ a * ν b else 0) ≤ μ a := by
  calc
    _ ≤ ∑ b, μ a * ν b := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hμ a) (hν b)
    _ = μ a := product_row μ ν htotal a

end Independent

end WeldedPath.CouplingHarmonic

end


-- Solutions.CouplingChain
section

namespace FiniteCouplingChain

open scoped BigOperators

theorem exists_adjacent_change {X : Type*} {T : ℕ} (p : Fin (T + 1) → X)
    (hne : p 0 ≠ p (Fin.last T)) :
    ∃ i : Fin T, p i.castSucc ≠ p i.succ := by
  by_contra h
  push Not at h
  have hall (i : Fin (T + 1)) : p i = p 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (h i).symm.trans ih
  exact hne (hall (Fin.last T)).symm

theorem endpoint_indicator_le {X : Type*} [DecidableEq X] {T : ℕ}
    (p : Fin (T + 1) → X) (v : ℝ) (hv : 0 ≤ v) :
    (if p 0 ≠ p (Fin.last T) then v else 0) ≤
      ∑ i : Fin T, if p i.castSucc ≠ p i.succ then v else 0 := by
  by_cases he : p 0 = p (Fin.last T)
  · simp only [he, ne_eq, not_true_eq_false, if_false]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  · obtain ⟨i, hi⟩ := exists_adjacent_change p he
    simp only [he, ne_eq, not_false_eq_true, if_true]
    have hs := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin T => if p j.castSucc ≠ p j.succ then v else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
    simpa only [if_pos hi] using hs

theorem weighted_endpoint_le {Ω X : Type*} [Fintype Ω] [DecidableEq X] {T : ℕ}
    (v : Ω → ℝ) (hv : ∀ ω, 0 ≤ v ω) (p : Ω → Fin (T + 1) → X)
    (b : Fin T → ℝ)
    (hstep : ∀ i, (∑ ω, if p ω i.castSucc ≠ p ω i.succ then v ω else 0) ≤ b i) :
    (∑ ω, if p ω 0 ≠ p ω (Fin.last T) then v ω else 0) ≤ ∑ i, b i := by
  calc
    _ ≤ ∑ ω, ∑ i : Fin T, if p ω i.castSucc ≠ p ω i.succ then v ω else 0 :=
      Finset.sum_le_sum (fun ω _ => endpoint_indicator_le (p ω) (v ω) (hv ω))
    _ = ∑ i : Fin T, ∑ ω, if p ω i.castSucc ≠ p ω i.succ then v ω else 0 :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hstep i)

section Pushforward

variable {H G Ω : Type*} [Fintype H] [Fintype G] [Fintype Ω] [DecidableEq G]

noncomputable def endpointWeight (v : H → Ω → ℝ) (out : Ω → G) (h : H) (g : G) : ℝ :=
  ∑ ω, if out ω = g then v h ω else 0

theorem endpointWeight_nonneg (v : H → Ω → ℝ) (out : Ω → G)
    (hv : ∀ h ω, 0 ≤ v h ω) (h : H) (g : G) : 0 ≤ endpointWeight v out h g := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hv h ω
  · exact le_rfl

theorem endpointWeight_row (v : H → Ω → ℝ) (out : Ω → G) (h : H) :
    (∑ g, endpointWeight v out h g) = ∑ ω, v h ω := by
  unfold endpointWeight
  rw [Finset.sum_comm]
  simp

theorem endpointWeight_test (v : H → Ω → ℝ) (out : Ω → G) (h : H)
    (P : G → Prop) [DecidablePred P] :
    (∑ g, if P g then endpointWeight v out h g else 0) =
      ∑ ω, if P (out ω) then v h ω else 0 := by
  unfold endpointWeight
  calc
    _ = ∑ g, ∑ ω, if out ω = g then (if P g then v h ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hp : P g <;> simp [hp]
    _ = _ := by
      rw [Finset.sum_comm]
      simp

end Pushforward

end FiniteCouplingChain

end


-- Solutions.WeldedPathCouplingReduction
section

namespace WeldedPath

open Classical QAlgorithms QAlgorithms.QueryHybrid CouplingLift CouplingHarmonic
open FiniteCouplingChain
open scoped BigOperators

/-- The switching certificate yields the full oracle coupling, with absolute constant 16. -/
theorem single_cycle_coupling_reduction :
    ∃ K : ℝ, 0 < K ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
      ∃ w : (Equiv.Perm (Label n) × Equiv.Perm G.edges) →
          (Equiv.Perm (Label n) × Equiv.Perm G.edges) → ℝ,
        (∀ σh σg, 0 ≤ w σh σg) ∧
        (∀ σh, (∑ σg, w σh σg) =
          if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0) ∧
        (∀ σg, (∑ σh, w σh σg) =
          if σg ∈ G.prodSupport l then 1 / ((G.prodSupport l).card : ℝ) else 0) ∧
        (∀ σh (x : Qubits (2 * n + 1) × Fin 3),
          (∑ σg, if G.oracleFn l σg x ≠ G.oracleFn l σh x then w σh σg else 0) ≤
            (K * (n : ℝ) / (2 : ℝ) ^ n) *
              (if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0)) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n l hn hl hln G hG hS
  have hnpos : 1 ≤ n := by omega
  obtain ⟨v, hv, hrow, hend, hcol, hstep⟩ :=
    single_cycle_switching_chain n l hn hl hln G hG hS
  let out : (Fin (2 ^ n + 1) → Equiv.Perm G.edges) → Equiv.Perm G.edges := fun p => p 0
  let w : Equiv.Perm G.edges → Equiv.Perm G.edges → ℝ := endpointWeight v out
  have hw : ∀ π ρ, 0 ≤ w π ρ := endpointWeight_nonneg v out hv
  have hr : ∀ π, (∑ ρ, w π ρ) = uniformWeight (edgeSingSupport l G) π := by
    intro π
    rw [show (∑ ρ, w π ρ) = ∑ p, v π p from endpointWeight_row v out π]
    convert hrow π using 1 <;>
      simp only [uniformWeight, edgeSingSupport, edgeProdSupport] <;> congr
  have hc : ∀ ρ, (∑ π, w π ρ) = uniformWeight (edgeProdSupport l G) ρ := by
    intro ρ
    convert hcol ρ using 1 <;>
      simp only [w, endpointWeight, out, uniformWeight, edgeProdSupport] <;> congr
  have hf (π : Equiv.Perm G.edges) (e : G.edges) :
      (∑ ρ, if ρ e ≠ π e then w π ρ else 0) ≤
        (16 * (n : ℝ) / (2 : ℝ) ^ n) * uniformWeight (edgeSingSupport l G) π := by
    calc
      _ = ∑ p, if (p 0) e ≠ π e then v π p else 0 :=
        endpointWeight_test v out π (fun ρ => ρ e ≠ π e)
      _ = ∑ p, if (p 0) e ≠ (p (Fin.last (2 ^ n))) e then v π p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hz : v π p = 0
        · simp [hz]
        · simp only [hend π p hz]
      _ ≤ ∑ i : Fin (2 ^ n),
          (4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1))) *
            uniformWeight (edgeSingSupport l G) π := by
        apply weighted_endpoint_le (v π) (hv π) (fun p i => (p i) e)
        intro i
        convert hstep π e i using 1 <;>
          simp only [uniformWeight, edgeSingSupport, edgeProdSupport] <;> congr
      _ = (∑ i : Fin (2 ^ n), 4 / ((2 : ℝ) ^ n * ((i.val : ℝ) + 1))) *
          uniformWeight (edgeSingSupport l G) π := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (dyadic_certificate_sum_le n hnpos)
        (uniformWeight_nonneg _ _)
  have hi (π : Equiv.Perm G.edges) (e : G.edges) :
      (∑ ρ, if ρ.symm e ≠ π.symm e then w π ρ else 0) ≤
        (16 * (n : ℝ) / (2 : ℝ) ^ n) * uniformWeight (edgeSingSupport l G) π := by
    have heq (ρ : Equiv.Perm G.edges) :
        ρ.symm e = π.symm e ↔ ρ (π.symm e) = π (π.symm e) := by
      constructor
      · intro h
        simpa only [ρ.apply_symm_apply, π.apply_symm_apply] using (congrArg ρ h).symm
      · intro h
        apply ρ.injective
        simpa only [ρ.apply_symm_apply, π.apply_symm_apply] using h.symm
    simpa only [ne_eq, ← heq] using hf π (π.symm e)
  refine ⟨liftWeight G w, liftWeight_nonneg G w hw, ?_, ?_, ?_⟩
  · intro σh
    simpa only [uniformWeight] using liftWeight_row l G w hr σh
  · intro σg
    simpa only [uniformWeight] using liftWeight_col l G w hc σg
  · intro σh x
    simpa only [uniformWeight] using
      liftWeight_disagreement l G w (16 * (n : ℝ) / (2 : ℝ) ^ n)
        (by positivity) hw hf hi σh x

end WeldedPath

end

open WeldedPath QAlgorithms
open scoped BigOperators

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid → (G.singSupport l).Nonempty →
      ∃ w : (Equiv.Perm (Label n) × Equiv.Perm G.edges) →
          (Equiv.Perm (Label n) × Equiv.Perm G.edges) → ℝ,
        (∀ σh σg, 0 ≤ w σh σg) ∧
        (∀ σh, (∑ σg, w σh σg) =
          if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0) ∧
        (∀ σg, (∑ σh, w σh σg) =
          if σg ∈ G.prodSupport l then 1 / ((G.prodSupport l).card : ℝ) else 0) ∧
        (∀ σh (x : Qubits (2 * n + 1) × Fin 3),
          (∑ σg, if G.oracleFn l σg x ≠ G.oracleFn l σh x then w σh σg else 0) ≤
            (K * (n : ℝ) / (2 : ℝ) ^ n) *
              (if σh ∈ G.singSupport l then 1 / ((G.singSupport l).card : ℝ) else 0)) := by
  exact WeldedPath.single_cycle_coupling_reduction
