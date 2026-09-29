-- Prove2me | solution 1 for ScenarioReduction.TernaryTree.redCost_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T19:44:01.954907+00:00
-- url     : https://prove2.me/submissions/ad470b88-3d5e-43af-aee1-f31a48737647

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_IStarStar
import Definitions.Def_ScenarioReduction_TernaryTree_redCost



namespace ScenarioReduction.TernaryTree

open Finset

variable {K : ℕ}

lemma scen_sub (δ : ℕ → ℝ) (σ τ : Fin K → Fin 3) (k : Fin (K + 1)) :
    (scenario δ σ - scenario δ τ) k =
      ∑ r ∈ univ.filter (fun r : Fin K => r.val < k.val),
        (((σ r : ℕ) : ℝ) - (τ r : ℕ)) * δ (r.val + 1) := by
  simp only [Pi.sub_apply, scenario, ← sum_sub_distrib]
  apply sum_congr rfl; intro r _; ring

theorem dist_ge_delta_k0 (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 3) (hστ : σ ≠ τ) :
    δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by
  classical
  have hex : ∃ m, ∃ hm : m < K, σ ⟨m, hm⟩ ≠ τ ⟨m, hm⟩ := by
    by_contra hc; push_neg at hc; exact hστ (funext fun i => hc i.val i.isLt)
  obtain ⟨hm, hne⟩ := Nat.find_spec hex
  set m := Nat.find hex
  have hagree : ∀ r : Fin K, r.val < m → σ r = τ r := by
    intro r hr
    have := Nat.find_min hex hr; push_neg at this; exact this r.isLt
  have hcoord : (scenario δ σ - scenario δ τ) ⟨m + 1, by omega⟩ =
      (((σ ⟨m, hm⟩ : ℕ) : ℝ) - (τ ⟨m, hm⟩ : ℕ)) * δ (m + 1) := by
    rw [scen_sub, sum_eq_single_of_mem (⟨m, hm⟩ : Fin K) (by simp)]
    intro r hr hrm
    simp only [mem_filter, mem_univ, true_and] at hr
    have : r.val < m := by
      have : r.val ≠ m := fun h => hrm (Fin.ext h)
      simp at hr; omega
    rw [hagree r this]; ring
  have key : ∀ a b : ℕ, a ≠ b → (1:ℝ) ≤ |(a:ℝ) - b| := by
    intro a b hab
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : (a:ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (b:ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have h1 := key _ _ (fun h => hne (Fin.ext h))
  have hδm := hδ (m + 1) (by rw [mem_Icc]; omega)
  have hk := hmin (m + 1) (by rw [mem_Icc]; omega)
  have h2 := norm_le_pi_norm (scenario δ σ - scenario δ τ) ⟨m + 1, by omega⟩
  rw [hcoord, Real.norm_eq_abs, abs_mul, abs_of_nonneg hδm] at h2
  nlinarith

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 3 ^ K) (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty)
    (hcard : J.card = 3 ^ K - n) :
    ((3 : ℝ) ^ K - n) / 3 ^ K * δ k0 ≤
      redCost (fun _ => 1 / (3 : ℝ) ^ K) (fun i j => ‖scenario δ i - scenario δ j‖) J hJ := by
  unfold redCost
  have hterm : ∀ σ ∈ J, (1 / (3 ^ K : ℝ)) * δ k0 ≤
      (1 / (3 ^ K : ℝ)) * Jᶜ.inf' hJ (fun τ => ‖scenario δ σ - scenario δ τ‖) := by
    intro σ hσ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_inf'; intro τ hτ
    apply dist_ge_delta_k0 K δ hδ k0 hk0 hmin
    rintro rfl; rw [mem_compl] at hτ; exact hτ hσ
  refine le_trans ?_ (sum_le_sum hterm)
  rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hn.le]; push_cast
  apply le_of_eq; ring


lemma two_coord (δ : ℕ → ℝ) (σ τ : Fin K → Fin 3) (i0 iX : Fin K) (hne : i0 ≠ iX)
    (hag : ∀ r, r ≠ i0 → r ≠ iX → σ r = τ r) (k : Fin (K + 1)) :
    (scenario δ σ - scenario δ τ) k =
      (if i0.val < k.val then (((σ i0 : ℕ) : ℝ) - (τ i0 : ℕ)) * δ (i0.val + 1) else 0) +
      (if iX.val < k.val then (((σ iX : ℕ) : ℝ) - (τ iX : ℕ)) * δ (iX.val + 1) else 0) := by
  rw [scen_sub]
  have : ∀ r ∈ univ.filter (fun r : Fin K => r.val < k.val),
      (((σ r : ℕ) : ℝ) - (τ r : ℕ)) * δ (r.val + 1) =
      (if r = i0 then (((σ i0 : ℕ) : ℝ) - (τ i0 : ℕ)) * δ (i0.val + 1) else 0) +
      (if r = iX then (((σ iX : ℕ) : ℝ) - (τ iX : ℕ)) * δ (iX.val + 1) else 0) := by
    intro r _
    by_cases h1 : r = i0
    · subst h1; rw [if_pos rfl, if_neg hne]; ring
    · by_cases h2 : r = iX
      · subst h2; rw [if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, hag r h1 h2]; ring
  rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp only [mem_filter, mem_univ, true_and]

lemma norm_eq_of_coords (v : Fin (K + 1) → ℝ) (i0 iX : Fin K) (hlt : i0.val < iX.val)
    (x1 x2 d0 dm : ℝ)
    (hv : ∀ k : Fin (K + 1), v k = (if i0.val < k.val then x1 * d0 else 0) +
      (if iX.val < k.val then x2 * dm else 0))
    (hx1 : |x1| = 1) (hx2 : x2 = 0 ∨ x2 = -x1) (h0 : 0 ≤ d0) (h1 : d0 ≤ dm) (h2 : dm ≤ 2 * d0) :
    ‖v‖ = d0 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg h0]
    intro k
    rw [hv k, Real.norm_eq_abs]
    split_ifs with ha hb hb
    · rcases hx2 with rfl | rfl
      · rw [show x1 * d0 + 0 * dm = x1 * d0 by ring, abs_mul, hx1, abs_of_nonneg h0]; simp
      · rw [show x1 * d0 + -x1 * dm = x1 * (d0 - dm) by ring, abs_mul, hx1,
          abs_of_nonpos (show d0 - dm ≤ 0 by linarith)]; linarith
    · rw [add_zero, abs_mul, hx1, abs_of_nonneg h0]; simp
    · exfalso; omega
    · simp; linarith
  · have h := norm_le_pi_norm v ⟨i0.val + 1, by omega⟩
    rw [hv, if_pos (by simp), if_neg (by simp; omega), add_zero, Real.norm_eq_abs, abs_mul, hx1,
      abs_of_nonneg h0, one_mul] at h
    exact h

lemma partner_gen (δ : ℕ → ℝ) (j : Fin K → Fin 3) (i0 iX : Fin K) (hlt : i0.val < iX.val)
    (v0 vX : Fin 3)
    (hx1 : |((v0 : ℕ) : ℝ) - (j i0 : ℕ)| = 1)
    (hx2 : ((vX : ℕ) : ℝ) - (j iX : ℕ) = 0 ∨
      ((vX : ℕ) : ℝ) - (j iX : ℕ) = -(((v0 : ℕ) : ℝ) - (j i0 : ℕ)))
    (h0 : 0 ≤ δ (i0.val + 1)) (h1 : δ (i0.val + 1) ≤ δ (iX.val + 1))
    (h2 : δ (iX.val + 1) ≤ 2 * δ (i0.val + 1)) :
    ‖scenario δ (Function.update (Function.update j i0 v0) iX vX) - scenario δ j‖ =
      δ (i0.val + 1) := by
  have hne : i0 ≠ iX := fun h => by rw [h] at hlt; omega
  have e0 : Function.update (Function.update j i0 v0) iX vX i0 = v0 := by
    rw [Function.update_of_ne hne, Function.update_self]
  have eX : Function.update (Function.update j i0 v0) iX vX iX = vX := Function.update_self _ _ _
  apply norm_eq_of_coords _ i0 iX hlt _ _ _ _ _ hx1 hx2 h0 h1 h2
  intro k
  rw [two_coord δ _ j i0 iX hne (fun r h1 h2 => by
    rw [Function.update_of_ne h2, Function.update_of_ne h1]) k, e0, eX]


def good (a b c : Fin 3) : Prop := (a = 1 ∧ b ≠ 1 ∧ c ≠ 1) ∨ (a ≠ 1 ∧ b = 1 ∧ c = 1)

instance (a b c : Fin 3) : Decidable (good a b c) := by unfold good; infer_instance

lemma isMid_iff (σ : Fin K → Fin 3) (r : Fin K) (l : ℕ) (h : r.val + 1 = l) :
    IsMid σ l ↔ σ r = 1 := by
  constructor
  · rintro ⟨r', h', hv⟩; have : r' = r := Fin.ext (by omega); rwa [this] at hv
  · intro hv; exact ⟨r, h, hv⟩

lemma isOuter_iff (σ : Fin K → Fin 3) (r : Fin K) (l : ℕ) (h : r.val + 1 = l) :
    IsOuter σ l ↔ σ r ≠ 1 := by
  constructor
  · rintro ⟨r', h', hv⟩; have : r' = r := Fin.ext (by omega); rwa [this] at hv
  · intro hv; exact ⟨r, h, hv⟩

lemma mem_ISS (K k0 : ℕ) (hk0 : 1 ≤ k0) (hK : k0 + 2 ≤ K) (σ : Fin K → Fin 3) :
    σ ∈ IStarStar K k0 ↔
      good (σ ⟨k0 - 1, by omega⟩) (σ ⟨k0, by omega⟩) (σ ⟨k0 + 1, by omega⟩) := by
  unfold IStarStar good
  simp only [mem_filter, mem_univ, true_and]
  rw [isMid_iff σ ⟨k0 - 1, by omega⟩ k0 (by simp; omega),
    isOuter_iff σ ⟨k0 - 1, by omega⟩ k0 (by simp; omega),
    isMid_iff σ ⟨k0, by omega⟩ (k0 + 1) rfl, isOuter_iff σ ⟨k0, by omega⟩ (k0 + 1) rfl,
    isMid_iff σ ⟨k0 + 1, by omega⟩ (k0 + 2) rfl, isOuter_iff σ ⟨k0 + 1, by omega⟩ (k0 + 2) rfl]

lemma f3a (a : Fin 3) (h : a ≠ 1) : |(((1 : Fin 3) : ℕ) : ℝ) - (a : ℕ)| = 1 := by
  fin_cases a <;> simp_all <;> norm_num
lemma f3b (a : Fin 3) (h : a ≠ 1) : |((a : ℕ) : ℝ) - ((1 : Fin 3) : ℕ)| = 1 := by
  fin_cases a <;> simp_all <;> norm_num
lemma f3c : |(((0 : Fin 3) : ℕ) : ℝ) - ((1 : Fin 3) : ℕ)| = 1 := by simp

theorem partner_in_IStarStar (K : ℕ) (hK : 3 ≤ K) (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (hk0K : k0 ≤ K - 2) (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStarStar K k0, ∃ i ∈ IStarStar K k0, ‖scenario δ i - scenario δ j‖ = δ k0 := by
  intro j hj
  rw [mem_Icc] at hk0
  have hK2 : k0 + 2 ≤ K := by omega
  have h0 := hδ k0 (by rw [mem_Icc]; omega)
  have hd1 := hmin (k0 + 1) (by rw [mem_Icc]; omega)
  have hd2 := hmin (k0 + 2) (by rw [mem_Icc]; omega)
  have hm1 := (le_max_left _ _).trans hmax
  have hm2 := (le_max_right _ _).trans hmax
  rw [mem_ISS K k0 hk0.1 hK2] at hj
  set i0 : Fin K := ⟨k0 - 1, by omega⟩ with hi0
  set i1 : Fin K := ⟨k0, by omega⟩ with hi1
  set i2 : Fin K := ⟨k0 + 1, by omega⟩ with hi2
  have e0 : i0.val + 1 = k0 := by simp [i0]; omega
  have e1 : i1.val + 1 = k0 + 1 := rfl
  have e2 : i2.val + 1 = k0 + 2 := rfl
  have n01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this; omega
  have n02 : i0 ≠ i2 := fun h => by have := congrArg Fin.val h; simp [i0, i2] at this <;> omega
  have n12 : i1 ≠ i2 := fun h => by have := congrArg Fin.val h; simp [i1, i2] at this
  have l01 : i0.val < i1.val := by simp [i0, i1]; omega
  have l02 : i0.val < i2.val := by simp [i0, i2]
  -- generic finisher
  have fin1 : ∀ (v0 vX : Fin 3), |((v0 : ℕ) : ℝ) - (j i0 : ℕ)| = 1 →
      (((vX : ℕ) : ℝ) - (j i1 : ℕ) = 0 ∨
        ((vX : ℕ) : ℝ) - (j i1 : ℕ) = -(((v0 : ℕ) : ℝ) - (j i0 : ℕ))) →
      good v0 vX (j i2) →
      ∃ i ∈ IStarStar K k0, ‖scenario δ i - scenario δ j‖ = δ k0 := by
    intro v0 vX hx1 hx2 hg
    refine ⟨Function.update (Function.update j i0 v0) i1 vX, ?_, ?_⟩
    · rw [mem_ISS K k0 hk0.1 hK2]
      rw [show (⟨k0 - 1, by omega⟩ : Fin K) = i0 from rfl, show (⟨k0, by omega⟩ : Fin K) = i1 from rfl,
        show (⟨k0 + 1, by omega⟩ : Fin K) = i2 from rfl]
      rw [Function.update_of_ne n01, Function.update_self, Function.update_self,
        Function.update_of_ne n12.symm, Function.update_of_ne n02.symm]
      exact hg
    · have := partner_gen δ j i0 i1 l01 v0 vX hx1 hx2 (by rw [e0]; exact h0)
        (by rw [e0, e1]; exact hd1) (by rw [e0, e1]; exact hm1)
      rw [e0] at this; exact this
  have fin2 : ∀ (v0 vX : Fin 3), |((v0 : ℕ) : ℝ) - (j i0 : ℕ)| = 1 →
      (((vX : ℕ) : ℝ) - (j i2 : ℕ) = 0 ∨
        ((vX : ℕ) : ℝ) - (j i2 : ℕ) = -(((v0 : ℕ) : ℝ) - (j i0 : ℕ))) →
      good v0 (j i1) vX →
      ∃ i ∈ IStarStar K k0, ‖scenario δ i - scenario δ j‖ = δ k0 := by
    intro v0 vX hx1 hx2 hg
    refine ⟨Function.update (Function.update j i0 v0) i2 vX, ?_, ?_⟩
    · rw [mem_ISS K k0 hk0.1 hK2]
      rw [show (⟨k0 - 1, by omega⟩ : Fin K) = i0 from rfl, show (⟨k0, by omega⟩ : Fin K) = i1 from rfl,
        show (⟨k0 + 1, by omega⟩ : Fin K) = i2 from rfl]
      rw [Function.update_of_ne n02, Function.update_self, Function.update_self,
        Function.update_of_ne n12, Function.update_of_ne n01.symm]
      exact hg
    · have := partner_gen δ j i0 i2 l02 v0 vX hx1 hx2 (by rw [e0]; exact h0)
        (by rw [e0, e2]; exact hd2) (by rw [e0, e2]; exact hm2)
      rw [e0] at this; exact this
  by_cases ha : j i0 = 1 <;> by_cases hb : j i1 = 1 <;> by_cases hc : j i2 = 1
  · -- M M M : set a := 0
    exact fin1 0 (j i1) (by rw [ha]; exact f3c) (Or.inl (sub_self _))
      (by unfold good; rw [hb, hc]; decide)
  · -- M M O : v0 = c at i0, set c := 1
    exact fin2 (j i2) 1 (by rw [ha]; exact f3b _ hc) (Or.inr (by rw [ha]; ring))
      (by unfold good; rw [hb]; simp [hc])
  · -- M O M : v0 = b, set b := 1
    exact fin1 (j i1) 1 (by rw [ha]; exact f3b _ hb) (Or.inr (by rw [ha]; ring))
      (by unfold good; rw [hc]; simp [hb])
  · -- M O O : in I**
    exact absurd (Or.inl ⟨ha, hb, hc⟩) hj
  · -- O M M : in I**
    exact absurd (Or.inr ⟨ha, hb, hc⟩) hj
  · -- O M O : set a := 1, b := a
    exact fin1 1 (j i0) (f3a _ ha) (Or.inr (by rw [hb]; ring))
      (by unfold good; simp [ha, hc])
  · -- O O M : set a := 1, c := a
    exact fin2 1 (j i0) (f3a _ ha) (Or.inr (by rw [hc]; ring))
      (by unfold good; simp [ha, hb])
  · -- O O O : set a := 1
    exact fin1 1 (j i1) (f3a _ ha) (Or.inl (sub_self _))
      (by unfold good; simp [hb, hc])

end ScenarioReduction.TernaryTree

open ScenarioReduction.TernaryTree

theorem solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 3 ^ K) (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty)
    (hcard : J.card = 3 ^ K - n) :
    ((3 : ℝ) ^ K - n) / 3 ^ K * δ k0 ≤
      redCost (fun _ => 1 / (3 : ℝ) ^ K) (fun i j => ‖scenario δ i - scenario δ j‖) J hJ := by
  exact redCost_lower_bound K δ hδ k0 hk0 hmin n hn J hJ hcard
