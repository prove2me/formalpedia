-- Prove2me | solution 1 for VecKnapsackMitM.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:44:25.883785+00:00
-- url     : https://prove2.me/submissions/8b4c23b9-4a4d-47b1-977f-5999e1c22498

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance

namespace Aux31

open VecKnapsackMitM.Main
open scoped Classical

noncomputable def fracSet {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Finset (Fin n) :=
  S.filter fun i => 0 < x i ∧ x i < 1

def FeasVec {d n : ℕ} (inst : Instance d n) (S : Finset (Fin n)) (δ : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 1) ∧
  (∀ t : Fin d, t.val + 1 < d →
    (∑ i ∈ S, x i * inst.w i t) ≤ (1 - δ) * inst.toItems.weight S t) ∧
  (1 - δ) * inst.toItems.profit S ≤ ∑ i ∈ S, x i * inst.p i

lemma reduce_step {d n : ℕ} (hd : 2 ≤ d) (inst : Instance d n) (S : Finset (Fin n)) (δ : ℝ)
    (x : Fin n → ℝ) (hx : FeasVec inst S δ x) (hcard : d ≤ (fracSet S x).card) :
    ∃ x' : Fin n → ℝ, FeasVec inst S δ x' ∧ (fracSet S x').card < (fracSet S x).card := by
  let F := fracSet S x
  have hmemF : ∀ i : Fin n, i ∈ F ↔ i ∈ S ∧ 0 < x i ∧ x i < 1 := by
    intro i; simp [F, fracSet]
  let L : (F → ℝ) →ₗ[ℝ] (Fin (d - 1) → ℝ) :=
    { toFun := fun v j => ∑ i : F, v i * inst.w i.1 ⟨j.val, by omega⟩
      map_add' := fun u v => by
        ext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext j; simp [mul_assoc, ← Finset.mul_sum] }
  have hfinrank : Module.finrank ℝ (Fin (d - 1) → ℝ) < Module.finrank ℝ (F → ℝ) := by
    simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_coe]
    change d - 1 < (fracSet S x).card
    omega
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hv_ker
  obtain ⟨dir, hdir_ne, hdir_ker, hdir_prof⟩ :
      ∃ dir : F → ℝ, dir ≠ 0 ∧ L dir = 0 ∧ 0 ≤ ∑ i : F, dir i * inst.p i.1 := by
    by_cases hp : 0 ≤ ∑ i : F, v i * inst.p i.1
    · exact ⟨v, hv_ne, hv_ker, hp⟩
    · refine ⟨-v, neg_ne_zero.mpr hv_ne, by rw [LinearMap.map_neg, hv_ker, neg_zero], ?_⟩
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      linarith
  let NZ : Finset F := Finset.univ.filter fun i : F => dir i ≠ 0
  have hNZ : NZ.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hdir_ne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let stepBound : F → ℝ := fun i => if 0 < dir i then (1 - x i.1) / dir i else -x i.1 / dir i
  obtain ⟨i_min, hi_min_mem, hi_min_le⟩ := Finset.exists_min_image NZ stepBound hNZ
  have hi_min_nz : dir i_min ≠ 0 := (Finset.mem_filter.mp hi_min_mem).2
  let lam : ℝ := stepBound i_min
  have hlam_pos : 0 < lam := by
    have hiF := (hmemF i_min.1).mp i_min.2
    dsimp [lam, stepBound]
    split_ifs with hpos
    · exact div_pos (by linarith) hpos
    · have hneg : dir i_min < 0 := lt_of_le_of_ne (not_lt.mp hpos) hi_min_nz
      exact div_pos_of_neg_of_neg (by linarith) hneg
  let x' : Fin n → ℝ := fun j => if hj : j ∈ F then x j + lam * dir ⟨j, hj⟩ else x j
  refine ⟨x', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hjS
    by_cases hjF : j ∈ F
    · simp only [x', hjF, ↓reduceDIte]
      have hxF := (hmemF j).mp hjF
      by_cases hdz : dir ⟨j, hjF⟩ = 0
      · rw [hdz, mul_zero, add_zero]
        exact ⟨hxF.2.1.le, hxF.2.2.le⟩
      · have hjNZ : (⟨j, hjF⟩ : F) ∈ NZ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdz⟩
        have hle_b := hi_min_le ⟨j, hjF⟩ hjNZ
        dsimp [stepBound] at hle_b
        by_cases hpos : 0 < dir ⟨j, hjF⟩
        · rw [if_pos hpos] at hle_b
          have hmul : lam * dir ⟨j, hjF⟩ ≤ 1 - x j := (le_div_iff₀ hpos).mp hle_b
          have hmul_pos : 0 < lam * dir ⟨j, hjF⟩ := mul_pos hlam_pos hpos
          constructor <;> linarith
        · rw [if_neg hpos] at hle_b
          have hneg : dir ⟨j, hjF⟩ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hdz
          have hmul : -x j ≤ lam * dir ⟨j, hjF⟩ := (le_div_iff_of_neg hneg).mp hle_b
          have hmul_neg : lam * dir ⟨j, hjF⟩ < 0 := mul_neg_of_pos_of_neg hlam_pos hneg
          constructor <;> linarith
    · simp only [x', hjF, ↓reduceDIte]
      exact hx.1 j hjS
  · intro t ht
    have hsum_eq : (∑ j ∈ S, x' j * inst.w j t) =
        (∑ j ∈ S, x j * inst.w j t) + lam * (L dir ⟨t.val, by omega⟩) := by
      have hFS : F ⊆ S := Finset.filter_subset _ _
      have hsplit : ∀ j ∈ S, x' j * inst.w j t = x j * inst.w j t +
          (if hj : j ∈ F then lam * (dir ⟨j, hj⟩ * inst.w j t) else 0) := by
        intro j _
        dsimp [x']
        split_ifs with hj <;> ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_subset hFS (fun j _ hj => by simp [hj])]
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
    rw [hsum_eq, hdir_ker, Pi.zero_apply, mul_zero, add_zero]
    exact hx.2.1 t ht
  · have hsum_eq : (∑ j ∈ S, x' j * inst.p j) =
        (∑ j ∈ S, x j * inst.p j) + lam * (∑ i : F, dir i * inst.p i.1) := by
      have hFS : F ⊆ S := Finset.filter_subset _ _
      have hsplit : ∀ j ∈ S, x' j * inst.p j = x j * inst.p j +
          (if hj : j ∈ F then lam * (dir ⟨j, hj⟩ * inst.p j) else 0) := by
        intro j _
        dsimp [x']
        split_ifs with hj <;> ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_subset hFS (fun j _ hj => by simp [hj]), Finset.mul_sum,
        ← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
    have hnonneg : 0 ≤ lam * (∑ i : F, dir i * inst.p i.1) := mul_nonneg hlam_pos.le hdir_prof
    linarith [hx.2.2]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro j hj'
      have hj'S : j ∈ S ∧ 0 < x' j ∧ x' j < 1 := by simpa [fracSet] using hj'
      by_contra hjF
      have hjnotF : j ∉ F := hjF
      have hxeq : x' j = x j := dif_neg hjnotF
      rw [hxeq] at hj'S
      exact hjF ((hmemF j).mpr hj'S)
    · intro heq
      have himin_in : i_min.1 ∈ fracSet S x' := by rw [heq]; exact i_min.2
      have himin_bounds : 0 < x' i_min.1 ∧ x' i_min.1 < 1 :=
        (Finset.mem_filter.mp himin_in).2
      have hx_imin : x' i_min.1 = x i_min.1 + lam * dir i_min := dif_pos i_min.2
      rw [hx_imin] at himin_bounds
      dsimp [lam, stepBound] at himin_bounds
      by_cases hpos : 0 < dir i_min
      · rw [if_pos hpos, div_mul_cancel₀ _ hi_min_nz] at himin_bounds
        linarith
      · rw [if_neg hpos, div_mul_cancel₀ _ hi_min_nz] at himin_bounds
        linarith

lemma exists_sparse_feas {d n : ℕ} (hd : 2 ≤ d) (inst : Instance d n) (S : Finset (Fin n)) (δ : ℝ) :
    ∀ (k : ℕ) (x : Fin n → ℝ), FeasVec inst S δ x → (fracSet S x).card ≤ k →
      ∃ x_star : Fin n → ℝ, FeasVec inst S δ x_star ∧ (fracSet S x_star).card ≤ d - 1
  | 0, x, hx, hle => ⟨x, hx, by omega⟩
  | k + 1, x, hx, hle => by
    by_cases hsmall : (fracSet S x).card ≤ d - 1
    · exact ⟨x, hx, hsmall⟩
    · have hge : d ≤ (fracSet S x).card := by omega
      obtain ⟨x', hx', hlt⟩ := reduce_step hd inst S δ x hx hge
      exact exists_sparse_feas hd inst S δ k x' hx' (by omega)

end Aux31

open VecKnapsackMitM.Main

theorem solution (d n : ℕ) (hd : 2 ≤ d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S : Finset (Fin n)) (hS : S.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Q ⊆ S,
      (∀ t : Fin d, t.val + 1 < d →
        inst.toItems.weight Q t ≤ (1 - δ) * inst.toItems.weight S t) ∧
      (1 - δ) * inst.toItems.profit S - ((d : ℝ) - 1) * S.sup' hS inst.p ≤
        inst.toItems.profit Q ∧
      (1 - δ) / d * inst.toItems.profit S ≤ max (inst.toItems.profit Q) (S.sup' hS inst.p) := by
  classical
  let x₀ : Fin n → ℝ := fun _ => 1 - δ
  have hx₀ : Aux31.FeasVec inst S δ x₀ := by
    refine ⟨fun _ _ => ⟨by linarith, by linarith⟩, fun t _ => ?_, ?_⟩
    · simp only [x₀, Items.weight, ← Finset.mul_sum]; exact le_rfl
    · simp only [x₀, Items.profit, ← Finset.mul_sum]; exact le_rfl
  obtain ⟨x, hx, hcard⟩ :=
    Aux31.exists_sparse_feas hd inst S δ (Aux31.fracSet S x₀).card x₀ hx₀ le_rfl
  let Q : Finset (Fin n) := S.filter fun i => x i = 1
  let F : Finset (Fin n) := Aux31.fracSet S x
  have hQS : Q ⊆ S := Finset.filter_subset _ _
  have hFS : F ⊆ S := Finset.filter_subset _ _
  have hdisj : Disjoint Q F := by
    rw [Finset.disjoint_left]
    intro i hiQ hiF
    have h1 : x i = 1 := (Finset.mem_filter.mp hiQ).2
    have hlt : x i < 1 := (Finset.mem_filter.mp hiF).2.2
    linarith
  have hprof_split : (∑ i ∈ S, x i * inst.p i) =
      inst.toItems.profit Q + ∑ i ∈ F, x i * inst.p i := by
    have hQF : Q ∪ F ⊆ S := Finset.union_subset hQS hFS
    rw [← Finset.sum_subset hQF, Finset.sum_union hdisj]
    · congr 1
      unfold Items.profit
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1 : x i = 1 := (Finset.mem_filter.mp hi).2
      rw [h1, one_mul]
    · intro i hiS hnot
      simp only [Finset.mem_union, not_or] at hnot
      have hbounds := hx.1 i hiS
      have hx0 : x i = 0 := by
        by_contra hne0
        have hpos : 0 < x i := lt_of_le_of_ne hbounds.1 (Ne.symm hne0)
        have hlt1 : x i < 1 := lt_of_le_of_ne hbounds.2 (fun h1 => hnot.1 (Finset.mem_filter.mpr ⟨hiS, h1⟩))
        exact hnot.2 (Finset.mem_filter.mpr ⟨hiS, hpos, hlt1⟩)
      rw [hx0, zero_mul]
  have hF_le : (∑ i ∈ F, x i * inst.p i) ≤ (F.card : ℝ) * S.sup' hS inst.p := by
    calc (∑ i ∈ F, x i * inst.p i)
        ≤ ∑ i ∈ F, S.sup' hS inst.p := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiS : i ∈ S := hFS hi
          have hx1 : x i ≤ 1 := (hx.1 i hiS).2
          have hp_nonneg : 0 ≤ inst.p i := hinst.1.1 i
          have hp_sup : inst.p i ≤ S.sup' hS inst.p := Finset.le_sup' inst.p hiS
          calc x i * inst.p i ≤ 1 * inst.p i := mul_le_mul_of_nonneg_right hx1 hp_nonneg
            _ = inst.p i := one_mul _
            _ ≤ S.sup' hS inst.p := hp_sup
      _ = (F.card : ℝ) * S.sup' hS inst.p := by simp
  have hsup_nonneg : 0 ≤ S.sup' hS inst.p := by
    obtain ⟨i₀, hi₀⟩ := hS
    exact (hinst.1.1 i₀).trans (Finset.le_sup' inst.p hi₀)
  have hcard_real : (F.card : ℝ) ≤ (d : ℝ) - 1 := by
    have hnat : F.card + 1 ≤ d := by dsimp [F]; omega
    have hr : (F.card : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hnat
    linarith
  refine ⟨Q, hQS, ?_, ?_, ?_⟩
  · intro t ht
    calc inst.toItems.weight Q t
        = ∑ i ∈ Q, 1 * inst.w i t := by simp [Items.weight]
      _ = ∑ i ∈ Q, x i * inst.w i t := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.mp hi).2]
      _ ≤ ∑ i ∈ S, x i * inst.w i t :=
          Finset.sum_le_sum_of_subset_of_nonneg hQS fun i hiS _ =>
            mul_nonneg (hx.1 i hiS).1 (hinst.1.2 i t)
      _ ≤ (1 - δ) * inst.toItems.weight S t := hx.2.1 t ht
  · have hF_bound : (∑ i ∈ F, x i * inst.p i) ≤ ((d : ℝ) - 1) * S.sup' hS inst.p :=
      hF_le.trans (mul_le_mul_of_nonneg_right hcard_real hsup_nonneg)
    linarith [hx.2.2, hprof_split]
  · let M : ℝ := max (inst.toItems.profit Q) (S.sup' hS inst.p)
    have hQM : inst.toItems.profit Q ≤ M := le_max_left _ _
    have hSM : S.sup' hS inst.p ≤ M := le_max_right _ _
    have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hF_bound : (∑ i ∈ F, x i * inst.p i) ≤ ((d : ℝ) - 1) * M := by
      calc (∑ i ∈ F, x i * inst.p i)
          ≤ ((d : ℝ) - 1) * S.sup' hS inst.p :=
            hF_le.trans (mul_le_mul_of_nonneg_right hcard_real hsup_nonneg)
        _ ≤ ((d : ℝ) - 1) * M :=
            mul_le_mul_of_nonneg_left hSM (by linarith)
    have hd_pos : (0 : ℝ) < d := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hd_pos]
    linarith [hx.2.2, hprof_split, hQM, hF_bound]
