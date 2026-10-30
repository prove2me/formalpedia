-- Prove2me | solution 1 for PochetWolsey.Decomposition.tu_box_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:07:47.194+00:00
-- url     : https://prove2.me/submissions/9b92726d-247f-42c3-b6ad-02f116159efc

import Mathlib

namespace S226P_6ac5bef5

open Filter Topology

lemma int_of_sign (s : SignType) : ∃ z : ℤ, (s : ℝ) = (z : ℝ) := by
  rcases s with _ | _ | _
  exacts [⟨0, by simp⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩]

end S226P_6ac5bef5

open Filter Topology Matrix in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℤ) (l h : Fin n → ℤ) (hA : A.IsTotallyUnimodular) :
    let P : Set (Fin n → ℝ) := {x | (∀ i, (∑ j, A i j * x j) ≤ (b i : ℝ)) ∧
      (∀ j, (l j : ℝ) ≤ x j) ∧ (∀ j, x j ≤ (h j : ℝ))}
    P.Nonempty → ∀ x ∈ Set.extremePoints ℝ P, ∀ j, ∃ z : ℤ, x j = (z : ℝ) := by
  classical
  intro P _ x hx j0
  by_contra hj0
  push_neg at hj0
  have hxP : x ∈ P := hx.1
  simp only [P, Set.mem_setOf_eq] at hxP
  obtain ⟨hrow, hl, hu⟩ := hxP
  -- integer entries
  have hAint : ∀ i j, ∃ z : ℤ, A i j = (z : ℝ) := by
    intro i j
    obtain ⟨s, hs⟩ := hA.apply i j
    obtain ⟨z, hz⟩ := S226P_6ac5bef5.int_of_sign s
    exact ⟨z, by rw [← hs, hz]⟩
  set S : Subring ℝ := (Int.castRingHom ℝ).range with hS
  have memS : ∀ r : ℝ, r ∈ S ↔ ∃ z : ℤ, r = (z : ℝ) := by
    intro r; rw [hS, RingHom.mem_range]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z, by rw [← hz]; simp⟩
    · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz]; simp⟩
  let p : Fin n → Prop := fun j => ∀ z : ℤ, x j ≠ (z : ℝ)
  let J := {j // p j}
  let T := {i // ∑ j, A i j * x j = (b i : ℝ)}
  let B : Matrix T J ℝ := fun i k => A i.1 k.1
  -- perturbation lemma
  have key : ∀ E : Fin n → ℝ, (∀ i, ∑ j, A i j * x j = (b i : ℝ) → ∑ j, A i j * E j = 0) →
      (∀ j, E j ≠ 0 → (l j : ℝ) < x j ∧ x j < h j) →
      ∀ᶠ ε in 𝓝 (0:ℝ), x + ε • E ∈ P := by
    intro E hE hEb
    have hexp : ∀ (i : Fin m) (ε : ℝ), ∑ j, A i j * (x + ε • E) j =
        ∑ j, A i j * x j + ε * ∑ j, A i j * E j := by
      intro i ε
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro j _; ring
    simp only [P, Set.mem_setOf_eq]
    refine ((Filter.eventually_all.2 fun i => ?_).and
      ((Filter.eventually_all.2 fun j => ?_).and (Filter.eventually_all.2 fun j => ?_)))
    · by_cases hi : ∑ j, A i j * x j = (b i : ℝ)
      · exact Filter.Eventually.of_forall fun ε => by rw [hexp, hE i hi, hi]; simp
      · have hlt : ∑ j, A i j * x j < (b i : ℝ) := lt_of_le_of_ne (hrow i) hi
        have hc : ContinuousAt (fun ε : ℝ => ∑ j, A i j * x j + ε * ∑ j, A i j * E j) 0 := by
          fun_prop
        have := hc.eventually_lt continuousAt_const (by simpa using hlt)
        exact this.mono fun ε hε => by rw [hexp]; exact hε.le
    · by_cases hj : E j = 0
      · exact Filter.Eventually.of_forall fun ε => by simp [hj, hl j]
      · have hc : ContinuousAt (fun ε : ℝ => x j + ε * E j) 0 := by fun_prop
        have := continuousAt_const.eventually_lt hc (by simpa using (hEb j hj).1)
        exact this.mono fun ε hε => by simpa using hε.le
    · by_cases hj : E j = 0
      · exact Filter.Eventually.of_forall fun ε => by simp [hj, hu j]
      · have hc : ContinuousAt (fun ε : ℝ => x j + ε * E j) 0 := by fun_prop
        have := hc.eventually_lt continuousAt_const (by simpa using (hEb j hj).2)
        exact this.mono fun ε hε => by simpa using hε.le
  -- strictness on J
  have hstrict : ∀ j, p j → (l j : ℝ) < x j ∧ x j < h j := by
    intro j hj
    exact ⟨lt_of_le_of_ne (hl j) (fun h' => hj (l j) h'.symm),
      lt_of_le_of_ne (hu j) (fun h' => hj (h j) h')⟩
  -- sum splitting
  have hsplit : ∀ (g : Fin n → ℝ), ∑ j, g j = ∑ k : J, g k.1 + ∑ k : {j // ¬ p j}, g k.1 :=
    fun g => (Fintype.sum_subtype_add_sum_subtype p g).symm
  by_cases hinj : ∀ d : J → ℝ, B *ᵥ d = 0 → d = 0
  · -- Case 2: integrality via Cramer
    -- rows span everything
    let r : T → (J → ℝ) := fun i => B i
    have hspan : Submodule.span ℝ (Set.range r) = ⊤ := by
      by_contra hne
      obtain ⟨f, hf0, hfm⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
        (lt_top_iff_ne_top.2 hne) inferInstance
      let d : J → ℝ := fun k => f (fun k' => if k = k' then 1 else 0)
      have hfd : ∀ v, f v = ∑ k, v k * d k := by
        intro v; rw [LinearMap.pi_apply_eq_sum_univ f v]; simp [d, smul_eq_mul]
      have hBd : B *ᵥ d = 0 := by
        funext i
        have : f (r i) = 0 := by
          have hmem : f (r i) ∈ (Submodule.span ℝ (Set.range r)).map f :=
            Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
          rw [hfm] at hmem; simpa using hmem
        rw [hfd] at this
        simpa [Matrix.mulVec, dotProduct, r] using this
      have := hinj d hBd
      apply hf0
      apply LinearMap.ext; intro v; rw [hfd]; simp [this]
    obtain ⟨bs, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range r)
    have hbfin : bs.Finite := (Set.finite_range r).subset hbsub
    let _ : Fintype bs := hbfin.fintype
    let basis := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
    have hcard : Fintype.card bs = Fintype.card J := by
      have h1 := Module.finrank_eq_card_basis basis
      rw [Module.finrank_fintype_fun_eq_card] at h1
      exact h1.symm
    let e : J ≃ bs := Fintype.equivOfCardEq hcard.symm
    have hg : ∀ v : bs, ∃ i : T, r i = v.1 := fun v => hbsub v.2
    let g : bs → T := fun v => Classical.choose (hg v)
    have hgr : ∀ v, r (g v) = v.1 := fun v => Classical.choose_spec (hg v)
    let M : Matrix J J ℝ := A.submatrix (fun j => (g (e j)).1) (fun k => k.1)
    have hMrow : ∀ j, M j = (e j).1 := by
      intro j; funext k
      have := congrFun (hgr (e j)) k
      simpa [M, r, B] using this
    have hMunit : IsUnit M := by
      rw [← Matrix.linearIndependent_rows_iff_isUnit]
      have : M.row = (Subtype.val : bs → (J → ℝ)) ∘ e := by
        funext j; exact hMrow j
      rw [this]
      exact hbli.comp e e.injective
    have hdet0 : M.det ≠ 0 := by
      rw [Matrix.isUnit_iff_isUnit_det] at hMunit; exact hMunit.ne_zero
    have hdet : M.det ∈ Set.range SignType.cast :=
      (Matrix.isTotallyUnimodular_iff_fintype A).1 hA J _ _
    -- integer matrix
    let Mi : Matrix J J ℤ := fun j k => Classical.choose (hAint (g (e j)).1 k.1)
    have hMi : (Int.castRingHom ℝ).mapMatrix Mi = M := by
      ext j k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
      exact (Classical.choose_spec (hAint (g (e j)).1 k.1)).symm
    have hadj : ∀ j k, M.adjugate j k ∈ S := by
      intro j k
      rw [← hMi, ← RingHom.map_adjugate]
      exact ⟨Mi.adjugate j k, rfl⟩
    let y : J → ℝ := fun k => x k.1
    have hc : ∀ j, (M *ᵥ y) j ∈ S := by
      intro j
      have htight := (g (e j)).2
      have hs := hsplit (fun k => A (g (e j)).1 k * x k)
      have hMy : (M *ᵥ y) j = ∑ k : J, A (g (e j)).1 k.1 * x k.1 := by
        simp [Matrix.mulVec, dotProduct, M, y]
      have hrest : ∑ k : {j // ¬ p j}, A (g (e j)).1 k.1 * x k.1 ∈ S := by
        apply Subring.sum_mem; intro k _
        apply S.mul_mem
        · obtain ⟨z, hz⟩ := hAint (g (e j)).1 k.1; exact (memS _).2 ⟨z, hz⟩
        · have := k.2; simp only [p, not_forall, not_not] at this
          obtain ⟨z, hz⟩ := this; exact (memS _).2 ⟨z, hz⟩
      have hbS : ((b (g (e j)).1 : ℤ) : ℝ) ∈ S := (memS _).2 ⟨_, rfl⟩
      rw [hMy]
      have : ∑ k : J, A (g (e j)).1 k.1 * x k.1 =
          (b (g (e j)).1 : ℝ) - ∑ k : {j // ¬ p j}, A (g (e j)).1 k.1 * x k.1 := by
        rw [← htight, hs]; ring
      rw [this]; exact S.sub_mem hbS hrest
    have hkey : M.det • y = M.adjugate *ᵥ (M *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hyS : ∀ k, M.det * y k ∈ S := by
      intro k
      have := congrFun hkey k
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      apply Subring.sum_mem; intro j _
      exact S.mul_mem (hadj k j) (hc j)
    obtain ⟨s, hs⟩ := hdet
    have hk := hyS ⟨j0, hj0⟩
    rcases s with _ | _ | _
    · exact hdet0 (by rw [← hs]; simp)
    · rw [← hs] at hk
      have hk' : -(x j0) ∈ S := by simpa [y] using hk
      obtain ⟨z, hz⟩ := (memS _).1 hk'
      exact hj0 (-z) (by push_cast; linarith)
    · rw [← hs] at hk
      have hk' : x j0 ∈ S := by simpa [y] using hk
      obtain ⟨z, hz⟩ := (memS _).1 hk'
      exact hj0 z hz
  · -- Case 1: perturbation contradicts extremality
    push_neg at hinj
    obtain ⟨d, hBd, hd0⟩ := hinj
    let D : Fin n → ℝ := fun j => if hj : p j then d ⟨j, hj⟩ else 0
    have hDJ : ∀ k : J, D k.1 = d k := fun k => by simp [D, k.2]
    have hDn : ∀ k : {j // ¬ p j}, D k.1 = 0 := fun k => by simp [D, k.2]
    have hDrow : ∀ i, ∑ j, A i j * x j = (b i : ℝ) → ∑ j, A i j * D j = 0 := by
      intro i hi
      rw [hsplit]
      have h2 : ∑ k : {j // ¬ p j}, A i k.1 * D k.1 = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [hDn k, mul_zero]
      rw [h2, add_zero]
      have := congrFun hBd ⟨i, hi⟩
      simpa [Matrix.mulVec, dotProduct, B, hDJ] using this
    have hDb : ∀ j, D j ≠ 0 → (l j : ℝ) < x j ∧ x j < h j := by
      intro j hj
      by_cases hpj : p j
      · exact hstrict j hpj
      · exact absurd (hDn ⟨j, hpj⟩) hj
    have hev1 := key D hDrow hDb
    have hev2 := key (-D) (fun i hi => by simp [hDrow i hi])
      (fun j hj => hDb j (by simpa using hj))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
    have hmem := hball (y := δ / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    obtain ⟨h1, h2⟩ := hmem
    have hseg : x ∈ openSegment ℝ (x + (δ / 2) • D) (x + (δ / 2) • -D) :=
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
        ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring⟩
    have := hx.2 h1 h2 hseg
    have hD0 : (δ / 2) • D = 0 := by
      have := congrArg (fun z => z - x) this; simpa using this
    apply hd0
    funext k
    have := congrFun hD0 k.1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · linarith
    · rw [← hDJ k, h]; rfl
