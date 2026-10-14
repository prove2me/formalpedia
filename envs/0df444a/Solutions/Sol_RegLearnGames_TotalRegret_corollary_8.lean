-- Prove2me | solution 1 for RegLearnGames.TotalRegret.corollary_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:28:39.394846+00:00
-- url     : https://prove2.me/submissions/974bb90b-3915-41fe-86d6-1af32970d1a9

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RRAux_RegLearnGames_TotalRegret_corollary_8

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

section Alg

variable {n : ℕ}

lemma e_sq (e c a : ℝ) (he : 0 ≤ e) (h : e ≤ c + a) : (1/8) * e ^ 2 ≤ (1/4) * (c ^ 2 + a ^ 2) := by
  nlinarith [sq_nonneg (c - a)]

lemma alg (hn : 2 ≤ n) (T : ℕ) (a c e B : Fin n → ℕ → ℝ) (ha : ∀ k t, 0 ≤ a k t)
    (hc : ∀ k t, 0 ≤ c k t) (he : ∀ k t, 0 ≤ e k t) (ha0 : ∀ k, a k 0 = 0)
    (hec : ∀ k t, e k t ≤ c k t + a k (t - 1)) (hB0 : ∀ i t, 0 ≤ B i t)
    (hB : ∀ i t, B i t ≤ (1/2) * ∑ k ∈ univ.erase i, e k t) :
    ∑ i, ∑ t ∈ Icc 1 T, (a i t * B i t - (a i t ^ 2 + c i t ^ 2) / (2 * (1 / (2 * ((n:ℝ) - 1)))))
      ≤ 0 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n:ℝ) - 1 with hmdef
  have hm : 0 < m := by linarith
  have hη : ∀ x : ℝ, x / (2 * (1 / (2 * m))) = x * m := by intro x; field_simp
  simp only [hη]
  set S : ℕ → ℝ := fun t => ∑ k, (c k t ^ 2 + a k (t - 1) ^ 2)
  have hterm : ∀ i t, a i t * B i t - (a i t ^ 2 + c i t ^ 2) * m ≤
      (1/4) * S t - (m / 2 * a i t ^ 2 + m * c i t ^ 2) := by
    intro i t
    have h1 := pt_bound (a i t) (B i t) (c i t) m hm
    have h2 := B_bound hn i (B i t) (fun k => e k t) (hB0 i t) (fun k => he k t) (hB i t)
    have h3 : (1/8) * ∑ k, e k t ^ 2 ≤ (1/4) * S t := by
      simp only [S, mul_sum]
      exact sum_le_sum fun k _ => e_sq _ _ _ (he k t) (hec k t)
    rw [← hmdef] at h2
    linarith
  have hsum : ∑ i, ∑ t ∈ Icc 1 T, (a i t * B i t - (a i t ^ 2 + c i t ^ 2) * m) ≤
      ∑ i, ∑ t ∈ Icc 1 T, ((1/4) * S t - (m / 2 * a i t ^ 2 + m * c i t ^ 2)) :=
    sum_le_sum fun i _ => sum_le_sum fun t _ => hterm i t
  have hshift : ∀ k, ∑ t ∈ Icc 1 T, a k (t - 1) ^ 2 ≤ ∑ t ∈ Icc 1 T, a k t ^ 2 := by
    intro k
    have := shift (fun t => a k t ^ 2) T
    simp only [ha0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
    nlinarith [sq_nonneg (a k T)]
  have hS : ∑ t ∈ Icc 1 T, S t ≤ ∑ k, ∑ t ∈ Icc 1 T, a k t ^ 2 + ∑ k, ∑ t ∈ Icc 1 T, c k t ^ 2 := by
    simp only [S]
    rw [sum_comm]
    simp only [sum_add_distrib]
    have := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin n))) => hshift k
    linarith
  set P := ∑ k, ∑ t ∈ Icc 1 T, a k t ^ 2
  set Q := ∑ k, ∑ t ∈ Icc 1 T, c k t ^ 2
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0 ≤ Q := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have e1 : ∑ i, ∑ t ∈ Icc 1 T, ((1/4) * S t - (m / 2 * a i t ^ 2 + m * c i t ^ 2)) =
      (n:ℝ) * ((1/4) * ∑ t ∈ Icc 1 T, S t) - (m / 2 * P + m * Q) := by
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, P, Q, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [e1] at hsum
  have h4 : (n:ℝ) * ((1/4) * ∑ t ∈ Icc 1 T, S t) ≤ (n:ℝ) * ((1/4) * (P + Q)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5 : (n:ℝ) * ((1/4) * (P + Q)) - (m / 2 * P + m * Q) =
      ((2 - n) / 4) * P + ((4 - 3 * n) / 4) * Q := by rw [hmdef]; ring
  have h6 : ((2 - n) / 4) * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hP
  have h7 : ((4 - 3 * n) / 4) * Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hQ
  linarith

end Alg

end RRAux_RegLearnGames_TotalRegret_corollary_8

open RegLearnGames.TotalRegret RRAux_RegLearnGames_TotalRegret_corollary_8 Finset in
theorem solution {n d : ℕ} (hn : 2 ≤ n) (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (h𝓡 : ∀ i, IsOneStronglyConvexL1 (𝓡 i))
    (R : ℝ) (hR : ∀ i, ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 i f - 𝓡 i g ≤ R)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : IsOFTRLDynamics u 𝓡 (1 / (2 * ((n : ℝ) - 1))) w)
    (T : ℕ) (wstar : Fin n → Fin d → ℝ) (hwstar : ∀ i, wstar i ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ∑ t ∈ Finset.Icc 1 T, (wstar i - w t i) ⬝ᵥ utilVec u (w t) i ≤
        n * R / (1 / (2 * ((n : ℝ) - 1))) ∧
      n * R / (1 / (2 * ((n : ℝ) - 1))) = 2 * n * ((n : ℝ) - 1) * R := by
  classical
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hη : (0:ℝ) < 1 / (2 * ((n : ℝ) - 1)) := by apply div_pos one_pos; linarith
  refine ⟨?_, by rw [div_div_eq_mul_div, div_one]; ring⟩
  have hmem : ∀ t k, w t k ∈ stdSimplex ℝ (Fin d) := by
    intro t k
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; exact (hw k).1.1
    · exact ((hw k).2 t h).1
  choose g hg hg0 using fun i => leader_exists (𝓡 i) (h𝓡 i) _ _ _ _ (hw i) hη
  set η := 1 / (2 * ((n : ℝ) - 1)) with hηdef
  let a : Fin n → ℕ → ℝ := fun i t => l1 (w t i - g i t)
  let c : Fin n → ℕ → ℝ := fun i t => l1 (g i (t - 1) - w t i)
  let e : Fin n → ℕ → ℝ := fun k t => l1 (w t k - w (t - 1) k)
  let B : Fin n → ℕ → ℝ := fun i t => (1/2) * ∑ k ∈ univ.erase i, e k t
  have hreg : ∀ i, ∑ t ∈ Icc 1 T, (wstar i - w t i) ⬝ᵥ utilVec u (w t) i ≤ R / η +
      ∑ t ∈ Icc 1 T, (a i t * B i t - (a i t ^ 2 + c i t ^ 2) / (2 * η)) := by
    intro i
    have h := rvu (𝓡 i) (h𝓡 i) η hη _ _ _ (g i) (hw i) (hg i) (hg0 i) T (wstar i) (hwstar i)
    have h1 : (𝓡 i (wstar i) - 𝓡 i (w 0 i)) / η ≤ R / η :=
      div_le_div_of_nonneg_right (hR i _ (hwstar i) _ (hmem 0 i)) hη.le
    have h2 : ∀ t ∈ Icc 1 T, (g i t - w t i) ⬝ᵥ (utilVec u (w t) i - utilVec u (w (t - 1)) i) -
        (l1 (w t i - g i t) ^ 2 + l1 (g i (t - 1) - w t i) ^ 2) / (2 * η) ≤
        a i t * B i t - (a i t ^ 2 + c i t ^ 2) / (2 * η) := by
      intro t _
      have := dot_le_l1 (g i t - w t i) (utilVec u (w t) i - utilVec u (w (t - 1)) i) (B i t)
        (fun x => by
        rw [Pi.sub_apply]
        exact util_diff u hu (w t) (w (t - 1)) (hmem t) (hmem (t - 1)) i x)
      rw [l1_sub_comm] at this
      simp only [a, c]
      linarith
    have h3 := sum_le_sum h2
    linarith
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => hreg i
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have halg := alg hn T a c e B (fun _ _ => l1_nonneg _) (fun _ _ => l1_nonneg _)
    (fun _ _ => l1_nonneg _) (fun k => by simp [a, hg0, l1])
    (fun k t => by
      have : w t k - w (t - 1) k = (w t k - g k (t - 1)) + (g k (t - 1) - w (t - 1) k) := by abel
      simp only [e, c, a]
      rw [this, l1_sub_comm (g k (t - 1)) (w t k), l1_sub_comm (w (t - 1) k) (g k (t - 1))]
      exact l1_add_le _ _)
    (fun i t => mul_nonneg (by norm_num) (sum_nonneg fun _ _ => l1_nonneg _))
    (fun i t => le_rfl)
  rw [mul_div_assoc]
  linarith

#print axioms solution
