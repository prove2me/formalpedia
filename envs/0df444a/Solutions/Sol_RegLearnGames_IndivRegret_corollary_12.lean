-- Prove2me | solution 1 for RegLearnGames.IndivRegret.corollary_12
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:32:28.572155+00:00
-- url     : https://prove2.me/submissions/b558b3ce-c029-4d8a-988e-6f6603bcefc9

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RRAux_RegLearnGames_IndivRegret_corollary_12

open Finset RegLearnGames.TotalRegret

variable {d : ℕ}

lemma l1_nonneg (v : Fin d → ℝ) : 0 ≤ l1 v := sum_nonneg fun _ _ => abs_nonneg _

lemma l1_smul (c : ℝ) (v : Fin d → ℝ) : l1 (c • v) = |c| * l1 v := by
  unfold l1; rw [mul_sum]; simp [abs_mul]

lemma l1_sub_comm (v w : Fin d → ℝ) : l1 (v - w) = l1 (w - v) := by
  unfold l1; simp [abs_sub_comm]

lemma l1_add_le (v w : Fin d → ℝ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1; rw [← sum_add_distrib]; exact sum_le_sum fun _ _ => abs_add_le _ _

lemma dot_le_l1 (v D : Fin d → ℝ) (B : ℝ) (hD : ∀ x, |D x| ≤ B) : v ⬝ᵥ D ≤ l1 v * B := by
  unfold l1 dotProduct; rw [sum_mul]
  refine sum_le_sum fun x _ => ?_
  calc v x * D x ≤ |v x * D x| := le_abs_self _
    _ = |v x| * |D x| := abs_mul _ _
    _ ≤ |v x| * B := mul_le_mul_of_nonneg_left (hD x) (abs_nonneg _)

lemma limit_aux (N D : ℝ) (hN : 0 ≤ N) (h : ∀ k : ℕ, N * (1 - (1/2:ℝ) ^ k) ≤ D) : N ≤ D := by
  by_contra hc
  push_neg at hc
  have hNpos : 0 < N := lt_of_le_of_lt (by linarith [h 0, show N * (1 - (1/2:ℝ)^0) = 0 by simp]) hc
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (N - D) / N by
    apply div_pos <;> linarith) (show (1/2:ℝ) < 1 by norm_num)
  have := h k
  rw [lt_div_iff₀ hNpos] at hk
  nlinarith

/-- Full strong concavity at a maximiser. -/
lemma sc_max (𝓡 : (Fin d → ℝ) → ℝ) (h𝓡 : IsOneStronglyConvexL1 𝓡) (η : ℝ) (hη : 0 < η)
    (X x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d))
    (hmax : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ X - 𝓡 v / η ≤ x ⬝ᵥ X - 𝓡 x / η) :
    ∀ v ∈ stdSimplex ℝ (Fin d),
      l1 (x - v) ^ 2 / (2 * η) ≤ (x ⬝ᵥ X - 𝓡 x / η) - (v ⬝ᵥ X - 𝓡 v / η) := by
  have key : ∀ k : ℕ, ∀ v ∈ stdSimplex ℝ (Fin d),
      l1 (x - v) ^ 2 / (2 * η) * (1 - (1/2:ℝ) ^ k) ≤ (x ⬝ᵥ X - 𝓡 x / η) - (v ⬝ᵥ X - 𝓡 v / η) := by
    intro k
    induction k with
    | zero => intro v hv; simp; linarith [hmax v hv]
    | succ k ih =>
      intro v hv
      have hm : (1/2:ℝ) • (x + v) ∈ stdSimplex ℝ (Fin d) := by
        have := (convex_stdSimplex ℝ (Fin d)) hx hv (show (0:ℝ) ≤ 1/2 by norm_num)
          (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
        convert this using 1; rw [smul_add]
      have hih := ih _ hm
      have hmid := h𝓡.2 x hx v hv
      have e1 : x - (1/2:ℝ) • (x + v) = (1/2:ℝ) • (x - v) := by
        rw [smul_add, smul_sub]; ext; simp; ring
      rw [e1, l1_smul] at hih
      have e2 : ((1/2:ℝ) • (x + v)) ⬝ᵥ X = (1/2) * (x ⬝ᵥ X + v ⬝ᵥ X) := by
        rw [smul_dotProduct, add_dotProduct, smul_eq_mul]
      rw [e2] at hih
      have hR : 𝓡 ((1/2:ℝ) • (x + v)) / η ≤ (𝓡 x + 𝓡 v) / 2 / η - l1 (x - v) ^ 2 / 8 / η := by
        rw [← sub_div]; exact div_le_div_of_nonneg_right hmid hη.le
      set N := l1 (x - v)
      set q := (1/2:ℝ) ^ k
      have hq : (1/2:ℝ) ^ (k+1) = q / 2 := by rw [pow_succ]; ring
      rw [hq]
      have e3 : (|(1/2:ℝ)| * N) ^ 2 / (2 * η) * (1 - q) = N ^ 2 / (2 * η) * (1 - q) / 4 := by
        rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]; ring
      rw [e3] at hih
      have e4 : N ^ 2 / (2 * η) * (1 - q / 2) =
          2 * (N ^ 2 / (2 * η) * (1 - q) / 4) + N ^ 2 / 8 / η * 2 := by
        field_simp; ring
      rw [e4]
      have e5 : (𝓡 x + 𝓡 v) / 2 / η = (𝓡 x / η + 𝓡 v / η) / 2 := by ring
      rw [e5] at hR
      linarith
  intro v hv
  exact limit_aux _ _ (by positivity) (fun k => key k v hv)

lemma rvu (𝓡 : (Fin d → ℝ) → ℝ) (h𝓡 : IsOneStronglyConvexL1 𝓡) (η : ℝ) (hη : 0 < η)
    (M u w g : ℕ → Fin d → ℝ) (hO : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g)
    (hg0 : g 0 = w 0) (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤ (𝓡 wstar - 𝓡 (w 0)) / η +
      ∑ t ∈ Icc 1 T, ((g t - w t) ⬝ᵥ (u t - M t) -
        (l1 (w t - g t) ^ 2 + l1 (g (t - 1) - w t) ^ 2) / (2 * η)) := by
  have claim : ∀ T : ℕ, g T ⬝ᵥ (∑ t ∈ Icc 1 T, u t) - 𝓡 (g T) / η ≤ - (𝓡 (w 0) / η) +
      ∑ t ∈ Icc 1 T, (w t ⬝ᵥ M t + g t ⬝ᵥ (u t - M t) -
        (l1 (w t - g t) ^ 2 + l1 (g (t - 1) - w t) ^ 2) / (2 * η)) := by
    intro T
    induction T with
    | zero => simp [hg0]
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      obtain ⟨hwS, hwmax⟩ := hO.2 (T + 1) (by omega)
      rw [Finset.Ico_add_one_right_eq_Icc] at hwmax
      set L := ∑ t ∈ Icc 1 T, u t
      have s1 := sc_max 𝓡 h𝓡 η hη _ _ hwS hwmax (g (T + 1)) (hg (T + 1)).1
      have s2 := sc_max 𝓡 h𝓡 η hη L (g T) (hg T).1 (hg T).2 (w (T + 1)) hwS
      simp only [Nat.add_sub_cancel] at *
      simp only [dotProduct_add, dotProduct_sub] at *
      have e : (l1 (w (T + 1) - g (T + 1)) ^ 2 + l1 (g T - w (T + 1)) ^ 2) / (2 * η) =
        l1 (w (T + 1) - g (T + 1)) ^ 2 / (2 * η) + l1 (g T - w (T + 1)) ^ 2 / (2 * η) := add_div _ _ _
      rw [e]
      linarith
  have h1 := (hg T).2 wstar hwstar
  have h2 := claim T
  have e1 : ∑ t ∈ Icc 1 T, (wstar - w t) ⬝ᵥ u t =
      wstar ⬝ᵥ (∑ t ∈ Icc 1 T, u t) - ∑ t ∈ Icc 1 T, w t ⬝ᵥ u t := by
    rw [dotProduct_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => sub_dotProduct _ _ _
  have e2 : ∑ t ∈ Icc 1 T, ((g t - w t) ⬝ᵥ (u t - M t) -
        (l1 (w t - g t) ^ 2 + l1 (g (t - 1) - w t) ^ 2) / (2 * η)) =
      ∑ t ∈ Icc 1 T, (w t ⬝ᵥ M t + g t ⬝ᵥ (u t - M t) -
        (l1 (w t - g t) ^ 2 + l1 (g (t - 1) - w t) ^ 2) / (2 * η)) -
      ∑ t ∈ Icc 1 T, w t ⬝ᵥ u t := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    simp only [sub_dotProduct, dotProduct_sub]
    ring
  rw [e1, e2, sub_div]
  linarith

section Marg

variable {n : ℕ}

noncomputable def Pr (σ : Fin n → Fin d → ℝ) (i : Fin n) (r : {j // j ≠ i} → Fin d) : ℝ :=
  ∏ j : {j // j ≠ i}, σ j.1 (r j)

lemma decomp (σ : Fin n → Fin d → ℝ) (i : Fin n) (f : (Fin n → Fin d) → ℝ) :
    ∑ s, AGT.profileProb σ s * f s =
      ∑ a, σ i a * ∑ r, Pr σ i r * f ((Equiv.funSplitAt i (Fin d)).symm (a, r)) := by
  rw [← (Equiv.funSplitAt i (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold AGT.profileProb Pr
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : (Equiv.funSplitAt i (Fin d)).symm (a, r) i = a := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have h2 : ∀ j : {j // j ≠ i}, (Equiv.funSplitAt i (Fin d)).symm (a, r) j.1 = r j := by
    intro j; simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  simp only [h1, h2]
  ring

lemma Pr_update (σ : Fin n → Fin d → ℝ) (i : Fin n) (v : Fin d → ℝ) (r : {j // j ≠ i} → Fin d) :
    Pr (Function.update σ i v) i r = Pr σ i r := by
  unfold Pr
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Function.update_of_ne j.2]

lemma Pr_nonneg (σ : Fin n → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (i : Fin n)
    (r : {j // j ≠ i} → Fin d) : 0 ≤ Pr σ i r :=
  prod_nonneg fun j _ => (hσ j.1).1 _

lemma Pr_sum (σ : Fin n → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ∑ r, Pr σ i r = 1 := by
  classical
  unfold Pr
  rw [← Fintype.prod_sum (fun (j : {j // j ≠ i}) (a : Fin d) => σ j.1 a)]
  exact prod_eq_one fun j _ => (hσ j.1).2

lemma one_coord (σ : Fin n → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (j : Fin n)
    (v : Fin d → ℝ) (hv : v ∈ stdSimplex ℝ (Fin d)) (f : (Fin n → Fin d) → ℝ)
    (hf : ∀ s, f s ∈ Set.Icc (0:ℝ) 1) :
    |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb (Function.update σ j v) s * f s|
      ≤ (1/2) * l1 (σ j - v) := by
  rw [decomp σ j, decomp _ j]
  simp only [Function.update_self, Pr_update]
  set K : Fin d → ℝ := fun a => ∑ r, Pr σ j r * f ((Equiv.funSplitAt j (Fin d)).symm (a, r))
  have hK0 : ∀ a, 0 ≤ K a := fun a =>
    sum_nonneg fun r _ => mul_nonneg (Pr_nonneg σ hσ j r) (hf _).1
  have hK1 : ∀ a, K a ≤ 1 := fun a => by
    calc K a ≤ ∑ r, Pr σ j r := sum_le_sum fun r _ =>
            mul_le_of_le_one_right (Pr_nonneg σ hσ j r) (hf _).2
      _ = 1 := Pr_sum σ hσ j
  have e : ∑ a, σ j a * K a - ∑ a, v a * K a = ∑ a, (σ j a - v a) * (K a - 1/2) := by
    have : ∑ a, (σ j a - v a) * (1/2:ℝ) = 0 := by
      rw [← sum_mul, sum_sub_distrib, (hσ j).2, hv.2]; ring
    simp only [mul_sub, sum_sub_distrib, this, sub_zero]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => by ring
  show |∑ a, σ j a * K a - ∑ a, v a * K a| ≤ _
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  unfold l1; rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [abs_mul, Pi.sub_apply]
  have : |K a - 1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith [hK0 a, hK1 a]
  calc |σ j a - v a| * |K a - 1/2| ≤ |σ j a - v a| * (1/2) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 1/2 * |σ j a - v a| := by ring

lemma multi_coord (f : (Fin n → Fin d) → ℝ) (hf : ∀ s, f s ∈ Set.Icc (0:ℝ) 1)
    (S : Finset (Fin n)) : ∀ σ τ : Fin n → Fin d → ℝ, (∀ k, σ k ∈ stdSimplex ℝ (Fin d)) →
      (∀ k, τ k ∈ stdSimplex ℝ (Fin d)) → (∀ k ∉ S, σ k = τ k) →
      |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb τ s * f s|
        ≤ (1/2) * ∑ k ∈ S, l1 (σ k - τ k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro σ τ _ _ h
    have : σ = τ := funext fun k => h k (by simp)
    subst this; simp
  | insert j S hj ih =>
    intro σ τ hσ hτ h
    set ρ := Function.update σ j (τ j)
    have hρ : ∀ k, ρ k ∈ stdSimplex ℝ (Fin d) := by
      intro k; by_cases hk : k = j
      · subst hk; simp [ρ, hτ]
      · simp [ρ, Function.update_of_ne hk, hσ]
    have hρτ : ∀ k ∉ S, ρ k = τ k := by
      intro k hk; by_cases hkj : k = j
      · subst hkj; simp [ρ]
      · simp only [ρ, Function.update_of_ne hkj]; exact h k (by simp [hkj, hk])
    have h1 := one_coord σ hσ j (τ j) (hτ j) f hf
    have h2 := ih ρ τ hρ hτ hρτ
    have e : ∑ k ∈ S, l1 (ρ k - τ k) = ∑ k ∈ S, l1 (σ k - τ k) := by
      refine sum_congr rfl fun k hk => ?_
      have : k ≠ j := fun h => hj (h ▸ hk)
      simp [ρ, Function.update_of_ne this]
    rw [e] at h2
    rw [sum_insert hj, mul_add]
    calc _ ≤ |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb ρ s * f s| +
          |∑ s, AGT.profileProb ρ s * f s - ∑ s, AGT.profileProb τ s * f s| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

end Marg

section Game

variable {n : ℕ}

lemma single_mem (x : Fin d) : (Pi.single x 1 : Fin d → ℝ) ∈ stdSimplex ℝ (Fin d) := by
  refine ⟨fun y => ?_, ?_⟩
  · by_cases h : y = x
    · subst h; simp
    · simp [Pi.single_apply, h]
  · simp

lemma util_diff (u : Fin n → (Fin n → Fin d) → ℝ) (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (σ τ : Fin n → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d))
    (hτ : ∀ k, τ k ∈ stdSimplex ℝ (Fin d)) (i : Fin n) (x : Fin d) :
    |utilVec u σ i x - utilVec u τ i x| ≤ (1/2) * ∑ k ∈ univ.erase i, l1 (σ k - τ k) := by
  have hσ' : ∀ k, Function.update σ i (Pi.single x 1) k ∈ stdSimplex ℝ (Fin d) := by
    intro k; by_cases hk : k = i
    · subst hk; simp [single_mem]
    · simp [Function.update_of_ne hk, hσ]
  have hτ' : ∀ k, Function.update τ i (Pi.single x 1) k ∈ stdSimplex ℝ (Fin d) := by
    intro k; by_cases hk : k = i
    · subst hk; simp [single_mem]
    · simp [Function.update_of_ne hk, hτ]
  have h := multi_coord (u i) (hu i) (univ.erase i) _ _ hσ' hτ' (by
    intro k hk
    have : k = i := by by_contra h; exact hk (by simp [h])
    subst this; simp)
  have e : ∑ k ∈ univ.erase i, l1 (Function.update σ i (Pi.single x 1) k -
      Function.update τ i (Pi.single x 1) k) = ∑ k ∈ univ.erase i, l1 (σ k - τ k) := by
    refine sum_congr rfl fun k hk => ?_
    have : k ≠ i := ne_of_mem_erase hk
    simp [Function.update_of_ne this]
  rw [e] at h
  exact h

lemma util_mem (u : Fin n → (Fin n → Fin d) → ℝ) (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (σ : Fin n → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (i : Fin n) (x : Fin d) :
    utilVec u σ i x ∈ Set.Icc (0:ℝ) 1 := by
  classical
  set σ' := Function.update σ i (Pi.single x 1)
  have hσ' : ∀ k, σ' k ∈ stdSimplex ℝ (Fin d) := by
    intro k; by_cases hk : k = i
    · subst hk; simp [σ', single_mem]
    · simp [σ', Function.update_of_ne hk, hσ]
  have hp : ∀ s, 0 ≤ AGT.profileProb σ' s := fun s => prod_nonneg fun j _ => (hσ' j).1 _
  have h1 : ∑ s, AGT.profileProb σ' s = 1 := by
    unfold AGT.profileProb; rw [← Fintype.prod_sum]; exact prod_eq_one fun j _ => (hσ' j).2
  show ∑ s, AGT.profileProb σ' s * u i s ∈ Set.Icc (0:ℝ) 1
  constructor
  · exact sum_nonneg fun s _ => mul_nonneg (hp s) (hu i s).1
  · calc ∑ s, AGT.profileProb σ' s * u i s ≤ ∑ s, AGT.profileProb σ' s :=
          sum_le_sum fun s _ => mul_le_of_le_one_right (hp s) (hu i s).2
      _ = 1 := h1

lemma leader_exists (𝓡 : (Fin d → ℝ) → ℝ) (h𝓡 : IsOneStronglyConvexL1 𝓡) (η : ℝ)
    (M u w : ℕ → Fin d → ℝ) (hO : IsOFTRL 𝓡 η M u w) (hη : 0 < η) :
    ∃ g : ℕ → Fin d → ℝ, IsLeader 𝓡 η u g ∧ g 0 = w 0 := by
  classical
  have hne : (stdSimplex ℝ (Fin d)).Nonempty := ⟨w 0, hO.1.1⟩
  have hex : ∀ T : ℕ, ∃ x ∈ stdSimplex ℝ (Fin d),
      IsMaxOn (fun v => v ⬝ᵥ (∑ t ∈ Icc 1 T, u t) - 𝓡 v / η) (stdSimplex ℝ (Fin d)) x := by
    intro T
    refine (isCompact_stdSimplex ℝ (Fin d)).exists_isMaxOn hne ?_
    refine ContinuousOn.sub ?_ (h𝓡.1.div_const η)
    exact (Continuous.dotProduct continuous_id continuous_const).continuousOn
  refine ⟨fun T => if T = 0 then w 0 else (hex T).choose, ?_, by simp⟩
  intro T
  by_cases hT : T = 0
  · subst hT
    simp only [if_true]
    refine ⟨hO.1.1, fun v hv => ?_⟩
    simp only [Finset.Icc_self, show Icc 1 0 = (∅ : Finset ℕ) by rfl, sum_empty, dotProduct_zero,
      zero_sub, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (hO.1.2 v hv) hη.le
  · simp only [hT, if_false]
    exact ⟨(hex T).choose_spec.1, fun v hv => (hex T).choose_spec.2 hv⟩

lemma shift (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Icc 1 T, f (t - 1) + f T = ∑ t ∈ Icc 1 T, f t + f 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    linarith

lemma pt_bound (a B c m : ℝ) (hm : 0 < m) :
    a * B - (a ^ 2 + c ^ 2) * m ≤ B ^ 2 / (2 * m) - m / 2 * a ^ 2 - m * c ^ 2 := by
  have : B ^ 2 / (2 * m) + m / 2 * a ^ 2 - a * B = (B - m * a) ^ 2 / (2 * m) := by
    field_simp; ring
  have h2 : 0 ≤ (B - m * a) ^ 2 / (2 * m) := by positivity
  linarith

lemma B_bound (hn : 2 ≤ n) (i : Fin n) (B : ℝ) (e : Fin n → ℝ) (hB0 : 0 ≤ B)
    (he : ∀ k, 0 ≤ e k) (hB : B ≤ (1/2) * ∑ k ∈ univ.erase i, e k) :
    B ^ 2 / (2 * ((n:ℝ) - 1)) ≤ (1/8) * ∑ k, e k ^ 2 := by
  have hm : (1:ℝ) ≤ (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcard : ((univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  have hX0 : 0 ≤ ∑ k ∈ univ.erase i, e k := sum_nonneg fun k _ => he k
  have h1 : B ^ 2 ≤ (1/4) * (∑ k ∈ univ.erase i, e k) ^ 2 := by nlinarith
  have h2 := sq_sum_le_card_mul_sum_sq (s := univ.erase i) (f := e)
  rw [hcard] at h2
  have h3 : ∑ k ∈ univ.erase i, e k ^ 2 ≤ ∑ k, e k ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ => sq_nonneg _
  have h4 : B ^ 2 ≤ (1/4) * (((n:ℝ) - 1) * ∑ k, e k ^ 2) := by
    have := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sum_nonneg fun k (_ : k ∈ (univ : Finset (Fin n))) => sq_nonneg (e k)]

end Game

section C12

variable {n : ℕ}

lemma stab (𝓡 : (Fin d → ℝ) → ℝ) (h𝓡 : IsOneStronglyConvexL1 𝓡) (η : ℝ) (hη : 0 < η)
    (X Y x y : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d)) (hy : y ∈ stdSimplex ℝ (Fin d))
    (hxm : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ X - 𝓡 v / η ≤ x ⬝ᵥ X - 𝓡 x / η)
    (hym : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ Y - 𝓡 v / η ≤ y ⬝ᵥ Y - 𝓡 y / η)
    (hXY : ∀ z, |(X - Y) z| ≤ 2) : l1 (x - y) ≤ 2 * η := by
  have s1 := sc_max 𝓡 h𝓡 η hη X x hx hxm y hy
  have s2 := sc_max 𝓡 h𝓡 η hη Y y hy hym x hx
  rw [l1_sub_comm] at s2
  have hd := dot_le_l1 (x - y) (X - Y) 2 hXY
  simp only [sub_dotProduct, dotProduct_sub] at hd
  set N := l1 (x - y)
  have hN : 0 ≤ N := l1_nonneg _
  have h3 : N ^ 2 / η ≤ N * 2 := by
    have : N ^ 2 / η = N ^ 2 / (2 * η) + N ^ 2 / (2 * η) := by field_simp; ring
    linarith
  rw [div_le_iff₀ hη] at h3
  by_contra hc
  push Not at hc
  nlinarith

lemma pt12 (a B c η : ℝ) (hη : 0 < η) :
    a * B - (a ^ 2 + c ^ 2) / (2 * η) ≤ η * B ^ 2 / 2 := by
  have : η * B ^ 2 / 2 + a ^ 2 / (2 * η) - a * B = (η * B - a) ^ 2 / (2 * η) := by
    field_simp; ring
  have h2 : 0 ≤ (η * B - a) ^ 2 / (2 * η) := by positivity
  have h3 : 0 ≤ c ^ 2 / (2 * η) := by positivity
  rw [add_div]
  linarith

lemma final12 (R p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    R / (p ^ (-(1:ℝ) / 2) * q ^ (-(1:ℝ) / 4)) +
        q * ((p ^ (-(1:ℝ) / 2) * q ^ (-(1:ℝ) / 4)) ^ 3 * p ^ 2 / 2) ≤
      (R + 4) * Real.sqrt p * q ^ ((1:ℝ) / 4) := by
  set A := Real.sqrt p with hA
  set Bq := q ^ ((1:ℝ) / 4) with hB
  have hA0 : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hB0 : 0 < Bq := Real.rpow_pos_of_pos (by linarith) _
  have hA2 : A ^ 2 = p := Real.sq_sqrt (by linarith)
  have hB4 : Bq ^ 4 = q := by
    rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have e1 : p ^ (-(1:ℝ) / 2) = A⁻¹ := by
    rw [show (-(1:ℝ) / 2) = -(1/2) by ring, Real.rpow_neg (by linarith), hA, Real.sqrt_eq_rpow]
  have e2 : q ^ (-(1:ℝ) / 4) = Bq⁻¹ := by
    rw [show (-(1:ℝ) / 4) = -(1/4) by ring, Real.rpow_neg (by linarith)]
  rw [e1, e2, ← hA2, ← hB4]
  have e3 : R / (A⁻¹ * Bq⁻¹) + Bq ^ 4 * ((A⁻¹ * Bq⁻¹) ^ 3 * (A ^ 2) ^ 2 / 2) =
      (R + 1/2) * A * Bq := by
    field_simp
  rw [e3]
  have : 0 < A * Bq := mul_pos hA0 hB0
  nlinarith

end C12

end RRAux_RegLearnGames_IndivRegret_corollary_12

open RegLearnGames.TotalRegret RRAux_RegLearnGames_IndivRegret_corollary_12 Finset in
theorem solution {n d : ℕ} (hn : 2 ≤ n) (T : ℕ) (hT : 1 ≤ T)
    (u : Fin n → (Fin n → Fin d) → ℝ) (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (h𝓡 : ∀ i, RegLearnGames.TotalRegret.IsOneStronglyConvexL1 (𝓡 i)) (R : ℝ)
    (hR : ∀ i, ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 i f - 𝓡 i g ≤ R)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : RegLearnGames.TotalRegret.IsOFTRLDynamics u 𝓡
      (((n : ℝ) - 1) ^ (-(1 : ℝ) / 2) * (T : ℝ) ^ (-(1 : ℝ) / 4)) w) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        (R + 4) * Real.sqrt ((n : ℝ) - 1) * (T : ℝ) ^ ((1 : ℝ) / 4) := by
  classical
  intro i wstar hwstar
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hη : (0:ℝ) < ((n : ℝ) - 1) ^ (-(1 : ℝ) / 2) * (T : ℝ) ^ (-(1 : ℝ) / 4) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
  have hfin := final12 R ((n:ℝ) - 1) T (by linarith) hT'
  set η := ((n : ℝ) - 1) ^ (-(1 : ℝ) / 2) * (T : ℝ) ^ (-(1 : ℝ) / 4) with hηdef
  have hmem : ∀ t k, w t k ∈ stdSimplex ℝ (Fin d) := by
    intro t k
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; exact (hw k).1.1
    · exact ((hw k).2 t h).1
  -- every iterate maximises against an explicit vector
  let Xf : Fin n → ℕ → Fin d → ℝ := fun k t =>
    if t = 0 then 0 else (∑ s ∈ Ico 1 t, utilVec u (w s) k) + utilVec u (w (t - 1)) k
  have hmax : ∀ k t, ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ Xf k t - 𝓡 k v / η ≤ w t k ⬝ᵥ Xf k t - 𝓡 k (w t k) / η := by
    intro k t v hv
    by_cases ht : t = 0
    · subst ht
      simp only [Xf, if_true, dotProduct_zero, zero_sub, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right ((hw k).1.2 v hv) hη.le
    · simp only [Xf, ht, if_false]
      exact ((hw k).2 t (Nat.pos_of_ne_zero ht)).2 v hv
  have hum : ∀ t k x, utilVec u (w t) k x ∈ Set.Icc (0:ℝ) 1 :=
    fun t k x => util_mem u hu (w t) (hmem t) k x
  have hdiff : ∀ k t, 1 ≤ t → ∀ z, |(Xf k t - Xf k (t - 1)) z| ≤ 2 := by
    intro k t ht z
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [Xf, Nat.add_sub_cancel, if_true, one_ne_zero, if_false, Pi.sub_apply,
        Pi.add_apply, Pi.zero_apply, sub_zero, Finset.Ico_self, sum_empty, zero_add]
      have := hum 0 k z
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
      have h1 : r + 1 + 1 ≠ 0 := by omega
      have h2 : r + 1 ≠ 0 := by omega
      simp only [Xf, h1, h2, if_false, Nat.add_sub_cancel]
      rw [Finset.sum_Ico_succ_top (by omega)]
      simp only [Pi.sub_apply, Pi.add_apply]
      have a1 := hum (r + 1) k z
      have a2 := hum r k z
      rw [abs_le]; constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
  have hstab : ∀ k t, 1 ≤ t → l1 (w t k - w (t - 1) k) ≤ 2 * η := fun k t ht =>
    stab (𝓡 k) (h𝓡 k) η hη _ _ _ _ (hmem t k) (hmem (t - 1) k) (hmax k t) (hmax k (t - 1))
      (hdiff k t ht)
  choose g hg hg0 using fun k => leader_exists (𝓡 k) (h𝓡 k) _ _ _ _ (hw k) hη
  have h := rvu (𝓡 i) (h𝓡 i) η hη _ _ _ (g i) (hw i) (hg i) (hg0 i) T wstar hwstar
  have h1 : (𝓡 i wstar - 𝓡 i (w 0 i)) / η ≤ R / η :=
    div_le_div_of_nonneg_right (hR i _ hwstar _ (hmem 0 i)) hη.le
  have hcard : ((univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  have h2 : ∀ t ∈ Icc 1 T, (g i t - w t i) ⬝ᵥ (utilVec u (w t) i - utilVec u (w (t - 1)) i) -
      (l1 (w t i - g i t) ^ 2 + l1 (g i (t - 1) - w t i) ^ 2) / (2 * η) ≤
      η ^ 3 * ((n:ℝ) - 1) ^ 2 / 2 := by
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
    set B := (1/2) * ∑ k ∈ univ.erase i, l1 (w t k - w (t - 1) k)
    have hd := dot_le_l1 (g i t - w t i) (utilVec u (w t) i - utilVec u (w (t - 1)) i) B
      (fun x => by
        rw [Pi.sub_apply]
        exact util_diff u hu (w t) (w (t - 1)) (hmem t) (hmem (t - 1)) i x)
    rw [l1_sub_comm] at hd
    have hp := pt12 (l1 (w t i - g i t)) B (l1 (g i (t - 1) - w t i)) η hη
    have hB0 : 0 ≤ B := mul_nonneg (by norm_num) (sum_nonneg fun _ _ => l1_nonneg _)
    have hB1 : B ≤ ((n:ℝ) - 1) * η := by
      have : ∑ k ∈ univ.erase i, l1 (w t k - w (t - 1) k) ≤ ∑ k ∈ univ.erase i, 2 * η :=
        sum_le_sum fun k _ => hstab k t ht1
      rw [sum_const, nsmul_eq_mul, hcard] at this
      simp only [B]; linarith
    have hB2 : η * B ^ 2 / 2 ≤ η ^ 3 * ((n:ℝ) - 1) ^ 2 / 2 := by
      have : B ^ 2 ≤ (((n:ℝ) - 1) * η) ^ 2 := pow_le_pow_left₀ hB0 hB1 2
      have := mul_le_mul_of_nonneg_left this hη.le
      nlinarith
    linarith
  have h3 := sum_le_sum h2
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul, show T + 1 - 1 = T by omega] at h3
  linarith

#print axioms solution
