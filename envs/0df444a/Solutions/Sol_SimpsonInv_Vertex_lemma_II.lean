-- Prove2me | solution 1 for SimpsonInv.Vertex.lemma_II
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:12:13.578236+00:00
-- url     : https://prove2.me/submissions/f4122254-95b2-4989-9b95-72f85524a641

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting



namespace SimpsonInv.Vertex

lemma sv_ext_affine {m : ℕ} (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (a • x + b • y) i = a * extVec S0 Sn x i + b * extVec S0 Sn y i := by
  unfold extVec
  split_ifs
  · linear_combination (-S0) * hab
  · simp
  · linear_combination (-Sn) * hab

lemma sv_rad_affine {m : ℕ} (T : ℕ → ℝ) (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (a • x + b • y) i
      = a * radicand T S0 Sn x i + b * radicand T S0 Sn y i := by
  unfold radicand
  rw [sv_ext_affine S0 Sn a b hab, sv_ext_affine S0 Sn a b hab]
  linear_combination (-(T i)) * hab

lemma sv_ext_shift {m : ℕ} (S0 Sn t : ℝ) (v d : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (v + t • d) i = extVec S0 Sn v i + t * extVec 0 0 d i := by
  unfold extVec
  split_ifs <;> simp

lemma sv_rad_shift {m : ℕ} (T : ℕ → ℝ) (S0 Sn t : ℝ) (v d : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (v + t • d) i
      = radicand T S0 Sn v i + t * (extVec 0 0 d (i - 1) - extVec 0 0 d i) := by
  unfold radicand
  rw [sv_ext_shift, sv_ext_shift]
  ring

lemma sv_strict_mid {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) (x y : Fin m → ℝ)
    (hx : x ∈ dom (m := m) T S0 Sn) (hy : y ∈ dom (m := m) T S0 Sn) (i0 : ℕ)
    (hi0 : i0 ∈ Finset.Icc 1 (m + 1)) (hne : radicand T S0 Sn x i0 ≠ radicand T S0 Sn y i0) :
    (1 / 2 : ℝ) * cost c r T S0 Sn x + (1 / 2 : ℝ) * cost c r T S0 Sn y
      < cost c r T S0 Sn ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
  have hab : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  unfold cost
  have e1 : (1 / 2 : ℝ) * (c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * Real.sqrt (radicand T S0 Sn x i)) +
      (1 / 2 : ℝ) * (c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * Real.sqrt (radicand T S0 Sn y i)) =
      c + ∑ i ∈ Finset.Icc 1 (m + 1), ((1 / 2 : ℝ) * (r i * Real.sqrt (radicand T S0 Sn x i)) + (1 / 2 : ℝ) * (r i * Real.sqrt (radicand T S0 Sn y i))) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e1]
  refine add_lt_add_of_le_of_lt le_rfl (Finset.sum_lt_sum (fun i hi => ?_) ⟨i0, hi0, ?_⟩)
  · rw [sv_rad_affine T S0 Sn _ _ hab]
    have h := Real.strictConcaveOn_sqrt.concaveOn.2 (show radicand T S0 Sn x i ∈ Set.Ici (0:ℝ) from hx.2 i hi)
      (show radicand T S0 Sn y i ∈ Set.Ici (0:ℝ) from hy.2 i hi) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) hab
    simp only [smul_eq_mul] at h
    calc _ = r i * ((1/2) * Real.sqrt (radicand T S0 Sn x i) + (1/2) * Real.sqrt (radicand T S0 Sn y i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (hr i hi).le
  · rw [sv_rad_affine T S0 Sn _ _ hab]
    have h := Real.strictConcaveOn_sqrt.2 (show radicand T S0 Sn x i0 ∈ Set.Ici (0:ℝ) from hx.2 i0 hi0)
      (show radicand T S0 Sn y i0 ∈ Set.Ici (0:ℝ) from hy.2 i0 hi0) hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) hab
    simp only [smul_eq_mul] at h
    calc _ = r i0 * ((1/2) * Real.sqrt (radicand T S0 Sn x i0) + (1/2) * Real.sqrt (radicand T S0 Sn y i0)) := by ring
      _ < _ := mul_lt_mul_of_pos_left h (hr i0 hi0)

lemma l2_sum_a {m : ℕ} (w : Fin m → ℝ) (i : ℕ) (hi : i ∈ Finset.Icc 1 (m + 1)) :
    ∑ k : Fin m, (if k.val + 2 = i then (1:ℝ) else 0) * w k = extVec 0 0 w (i - 1) := by
  rw [Finset.mem_Icc] at hi
  by_cases h : 2 ≤ i
  · have hk : i - 2 < m := by omega
    rw [Finset.sum_eq_single (⟨i - 2, hk⟩ : Fin m)]
    · have : i - 1 ≠ 0 := by omega
      have h2 : i - 1 ≤ m := by omega
      simp only [extVec, this, h2, dif_neg, dif_pos, not_false_eq_true]
      have : (⟨i - 1 - 1, by omega⟩ : Fin m) = ⟨i - 2, hk⟩ := by ext; simp; omega
      simp [this]
      omega
    · intro b _ hb
      have : b.val + 2 ≠ i := by
        intro e; apply hb; ext; simp; omega
      simp [this]
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun k _ => by
      have : k.val + 2 ≠ i := by omega
      simp [this]))
    have : i - 1 = 0 := by omega
    simp [extVec, this]

lemma l2_sum_b {m : ℕ} (w : Fin m → ℝ) (i : ℕ) (hi : i ∈ Finset.Icc 1 (m + 1)) :
    ∑ k : Fin m, (if k.val + 1 = i then (1:ℝ) else 0) * w k = extVec 0 0 w i := by
  rw [Finset.mem_Icc] at hi
  by_cases h : i ≤ m
  · have hk : i - 1 < m := by omega
    rw [Finset.sum_eq_single (⟨i - 1, hk⟩ : Fin m)]
    · have : i ≠ 0 := by omega
      simp [extVec, this, h]
      omega
    · intro b _ hb
      have : b.val + 1 ≠ i := by
        intro e; apply hb; ext; simp; omega
      simp [this]
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun k _ => by
      have : k.val + 1 ≠ i := by omega
      simp [this]))
    have : i ≠ 0 := by omega
    simp [extVec, this, h]

lemma l2_dual {m : ℕ} (f : Module.Dual ℝ (Fin m → ℝ)) (x : Fin m → ℝ) :
    f x = ∑ k : Fin m, x k * f (fun j => if k = j then 1 else 0) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp [smul_eq_mul]

theorem lemma_II_core {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (hm : 2 ≤ m)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) :
    ∀ v ∈ dom (m := m) T S0 Sn,
      IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v → 2 ≤ tightRank T S0 Sn v := by
  intro v hv hmin
  by_contra hlt
  push Not at hlt
  unfold tightRank at hlt
  set K := Submodule.span ℝ (tightNormals T S0 Sn v) with hK
  let nrm : ℕ → (Fin m → ℝ) := fun i k => (if k.val + 2 = i then (1:ℝ) else 0) - (if k.val + 1 = i then (1:ℝ) else 0)
  -- Step A
  have hA : ∃ i0 ∈ Finset.Icc 1 (m + 1), nrm i0 ∉ K := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    have h2 := hcon 2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    let g : Fin 2 → Fin m := ![⟨0, by omega⟩, ⟨1, by omega⟩]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [g] at hab ⊢
    have hli : LinearIndependent ℝ (fun a : Fin 2 => (Pi.basisFun ℝ (Fin m)) (g a)) :=
      (Pi.basisFun ℝ (Fin m)).linearIndependent.comp g hg
    have he0 : (Pi.basisFun ℝ (Fin m)) (g 0) ∈ K := by
      have : (Pi.basisFun ℝ (Fin m)) (g 0) = - nrm 1 := by
        ext k
        simp only [g, nrm, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff, Pi.neg_apply]
        simp only [Matrix.cons_val_zero]
        have a1 : (k:ℕ) + 2 ≠ 1 := by omega
        by_cases hk : (k:ℕ) = 0 <;> simp [a1, hk]
      rw [this]; exact K.neg_mem h1
    have he1 : (Pi.basisFun ℝ (Fin m)) (g 1) ∈ K := by
      have : (Pi.basisFun ℝ (Fin m)) (g 1) = (Pi.basisFun ℝ (Fin m)) (g 0) - nrm 2 := by
        ext k
        simp only [g, nrm, Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff, Pi.sub_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        by_cases hk : (k:ℕ) = 0 <;> by_cases hk1 : (k:ℕ) = 1 <;> simp [hk, hk1]
      rw [this]; exact K.sub_mem he0 h2
    have hsp : Submodule.span ℝ (Set.range (fun a : Fin 2 => (Pi.basisFun ℝ (Fin m)) (g a))) ≤ K := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      fin_cases a
      · exact he0
      · exact he1
    have := Submodule.finrank_mono hsp
    rw [finrank_span_eq_card hli] at this
    simp at this
    omega
  obtain ⟨i0, hi0, hn0⟩ := hA
  -- Step B
  obtain ⟨f, hf0, hfK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn0 inferInstance
  have hfK' : ∀ x ∈ K, f x = 0 := by
    intro x hx
    have : f x ∈ K.map f := Submodule.mem_map_of_mem hx
    rw [hfK] at this
    simpa using this
  set w : Fin m → ℝ := fun k => f (fun j => if k = j then 1 else 0) with hw
  have hfw : ∀ x, f x = ∑ k : Fin m, x k * w k := fun x => l2_dual f x
  -- Step C
  have hC : ∀ i ∈ Finset.Icc 1 (m + 1), f (nrm i) = extVec 0 0 w (i - 1) - extVec 0 0 w i := by
    intro i hi
    rw [hfw, ← l2_sum_a w i hi, ← l2_sum_b w i hi, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [nrm]; ring
  have hb0 : extVec 0 0 w (i0 - 1) - extVec 0 0 w i0 ≠ 0 := by
    rw [← hC i0 hi0]; exact hf0
  -- tight facts
  have hwj : ∀ j : Fin m, v j = 0 → w j = 0 := by
    intro j hj
    have hmem : (fun k : Fin m => if k = j then (1:ℝ) else 0) ∈ K := by
      apply Submodule.subset_span
      left
      exact ⟨j, hj, rfl⟩
    have := hfK' _ hmem
    rw [hfw] at this
    simpa [hw] using this
  have hwi : ∀ i ∈ Finset.Icc 1 (m + 1), radicand T S0 Sn v i = 0 →
      extVec 0 0 w (i - 1) - extVec 0 0 w i = 0 := by
    intro i hi hri
    have hmem : nrm i ∈ K := by
      apply Submodule.subset_span
      right
      exact ⟨i, hi, hri, rfl⟩
    rw [← hC i hi]
    exact hfK' _ hmem
  -- Step D
  have hev : ∀ᶠ t in nhds (0:ℝ), v + t • w ∈ dom (m := m) T S0 Sn := by
    have e1 : ∀ᶠ t in nhds (0:ℝ), ∀ j : Fin m, 0 ≤ (v + t • w) j := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : v j = 0
      · have := hwj j hj
        exact Filter.Eventually.of_forall (fun t => by simp [hj, this])
      · have hpos : 0 < v j := lt_of_le_of_ne (hv.1 j) (Ne.symm hj)
        have hc : ContinuousAt (fun t : ℝ => (v + t • w) j) 0 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          fun_prop
        have := (continuousAt_const (y := (0:ℝ))).eventually_lt hc (by simpa using hpos) |>.mono (fun t ht => ht.le)
        exact this
    have e2 : ∀ᶠ t in nhds (0:ℝ), ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ radicand T S0 Sn (v + t • w) i := by
      rw [Filter.eventually_all_finset]
      intro i hi
      by_cases hri : radicand T S0 Sn v i = 0
      · have := hwi i hi hri
        exact Filter.Eventually.of_forall (fun t => by rw [sv_rad_shift, hri, this]; simp)
      · have hpos : 0 < radicand T S0 Sn v i := lt_of_le_of_ne (hv.2 i hi) (Ne.symm hri)
        have hc : ContinuousAt (fun t : ℝ => radicand T S0 Sn (v + t • w) i) 0 := by
          have : (fun t : ℝ => radicand T S0 Sn (v + t • w) i) = fun t => radicand T S0 Sn v i + t * (extVec 0 0 w (i - 1) - extVec 0 0 w i) := by
            funext t; exact sv_rad_shift T S0 Sn t v w i
          rw [this]; fun_prop
        have := (continuousAt_const (y := (0:ℝ))).eventually_lt hc (by simpa [sv_rad_shift] using hpos) |>.mono (fun t ht => ht.le)
        exact this
    exact (e1.and e2).mono (fun t ht => ⟨ht.1, ht.2⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hx : v + (ε / 2) • w ∈ dom (m := m) T S0 Sn := hball (by simp [abs_of_pos hε]; linarith)
  have hy : v + (-(ε / 2)) • w ∈ dom (m := m) T S0 Sn := hball (by simp [abs_of_pos hε]; linarith)
  have hmid : (1 / 2 : ℝ) • (v + (ε / 2) • w) + (1 / 2 : ℝ) • (v + (-(ε / 2)) • w) = v := by
    ext k; simp; ring
  have hne : radicand T S0 Sn (v + (ε / 2) • w) i0 ≠ radicand T S0 Sn (v + (-(ε / 2)) • w) i0 := by
    rw [sv_rad_shift, sv_rad_shift]
    intro h
    apply hb0
    have : ε * (extVec 0 0 w (i0 - 1) - extVec 0 0 w i0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hε.ne'
    · exact h
  have key := sv_strict_mid c S0 Sn r T hr _ _ hx hy i0 hi0 hne
  rw [hmid] at key
  have a1 : cost c r T S0 Sn v ≤ cost c r T S0 Sn (v + (ε / 2) • w) := hmin hx
  have a2 : cost c r T S0 Sn v ≤ cost c r T S0 Sn (v + (-(ε / 2)) • w) := hmin hy
  linarith

end SimpsonInv.Vertex

open SimpsonInv.Vertex


theorem solution {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (hm : 2 ≤ m)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) :
    ∀ v ∈ dom (m := m) T S0 Sn,
      IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v → 2 ≤ tightRank T S0 Sn v := by
  exact lemma_II_core c S0 Sn r T hm hr
