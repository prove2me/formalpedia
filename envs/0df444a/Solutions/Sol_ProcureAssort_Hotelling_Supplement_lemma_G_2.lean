-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.lemma_G_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:23.519202+00:00
-- url     : https://prove2.me/submissions/1075c97b-f565-4ae7-aacf-e183a8ec4628

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (p : Fin n → ℝ) :
    let Q := M.active p
    Q.Nonempty ∧
    M.IsDemand Finset.univ p (M.demand Finset.univ p) ∧
    M.demand Finset.univ p = M.demand Q p ∧
    0 < (∑ i : Q, ∑ j : Q, M.faceF Q i j) ∧
    ∀ i : Q, M.demand Finset.univ p i = M.faceDemand Q p i := by
      intro Q
      obtain ⟨hα, hΓ, hoff⟩ := hM
      have hD : M.D.PosDef := hΓ.inv
      have hDsym : ∀ i j, M.D i j = M.D j i := by
        intro i j; have := hD.1.apply i j; simpa using this.symm
      have hq : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * M.D i j * v j := by
        intro v hv
        have := hD.dotProduct_mulVec_pos hv
        simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using this
      set φ : (Fin n → ℝ) → ℝ := fun y => M.gcs y - ∑ i, p i * y i with hφ
      have hexp : ∀ (x d : Fin n → ℝ) (t : ℝ), φ (fun k => x k + t * d k) = φ x
          + t * ∑ k, d k * (M.c k - p k - ∑ j, M.D k j * x j)
          - t^2 * (∑ i, ∑ j, d i * M.D i j * d j) / 2 := by
        intro x d t
        have hs : ∑ i, ∑ j, x i * M.D i j * d j = ∑ i, ∑ j, d i * M.D i j * x j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hDsym]; ring
        have h1 : ∑ i, ∑ j, (x i + t * d i) * M.D i j * (x j + t * d j)
            = ∑ i, ∑ j, x i * M.D i j * x j + t * ∑ i, ∑ j, x i * M.D i j * d j
              + t * ∑ i, ∑ j, d i * M.D i j * x j + t^2 * ∑ i, ∑ j, d i * M.D i j * d j := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          ring
        have h2 : ∑ k, d k * (M.c k - p k - ∑ j, M.D k j * x j)
            = ∑ k, M.c k * d k - ∑ k, p k * d k - ∑ i, ∑ j, d i * M.D i j * x j := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          · congr 1
            · exact Finset.sum_congr rfl (fun k _ => by ring)
            · exact Finset.sum_congr rfl (fun k _ => by ring)
          · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
        have h3 : ∑ k, M.c k * (x k + t * d k) = ∑ k, M.c k * x k + t * ∑ k, M.c k * d k := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        have h4 : ∑ k, p k * (x k + t * d k) = ∑ k, p k * x k + t * ∑ k, p k * d k := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        simp only [hφ, QuadraticMarket.gcs]
        rw [h1, h2, h3, h4, hs]; ring
      -- existence
      have hne : (stdSimplex ℝ (Fin n)).Nonempty := by
        refine ⟨fun k => if k = ⟨0, hn⟩ then 1 else 0, fun k => ?_, ?_⟩
        · dsimp only; split_ifs <;> norm_num
        · simp
      have hcont : ContinuousOn φ (stdSimplex ℝ (Fin n)) := by
        apply Continuous.continuousOn
        simp only [hφ, QuadraticMarket.gcs]; fun_prop
      obtain ⟨x0, hx0S, hx0max⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMaxOn hne hcont
      have hex : ∃ x, M.IsDemand Finset.univ p x := ⟨x0, hx0S, by simp, fun y hy _ => hx0max hy⟩
      have hdem : M.IsDemand Finset.univ p (M.demand Finset.univ p) := Classical.epsilon_spec hex
      set x := M.demand Finset.univ p with hx
      have hxS : x ∈ productSimplex (Fin n) := hdem.1
      have hxmax : ∀ y ∈ productSimplex (Fin n), φ y ≤ φ x := fun y hy => hdem.2.2 y hy (by simp)
      have hxnn : ∀ k, 0 ≤ x k := hxS.1
      have hxsum : ∑ k, x k = 1 := hxS.2
      have hQmem : ∀ k, k ∈ Q ↔ 0 < x k := by
        intro k; simp [Q, QuadraticMarket.active, x]
      have hxoff : ∀ k ∉ Q, x k = 0 := by
        intro k hk; rw [hQmem] at hk; linarith [hxnn k]
      have hQne : Q.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have : ∑ k, x k = 0 := Finset.sum_eq_zero (fun k _ => hxoff k (by simp [h]))
        linarith

      -- uniqueness on face Q
      have hxQ : M.IsDemand Q p x := ⟨hxS, hxoff, fun y hy _ => hxmax y hy⟩
      have hzQ : M.IsDemand Q p (M.demand Q p) := Classical.epsilon_spec ⟨x, hxQ⟩
      set z := M.demand Q p with hz
      have hxz : x = z := by
        by_contra hne
        have hd : (fun k => z k - x k) ≠ 0 := by
          intro h; apply hne; funext k; have := congrFun h k; simp at this; linarith
        have hqpos := hq _ hd
        have hmS : (fun k => x k + (1/2) * (z k - x k)) ∈ productSimplex (Fin n) := by
          refine ⟨fun k => ?_, ?_⟩
          · nlinarith [hxnn k, hzQ.1.1 k]
          · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hxsum, hzQ.1.2]
            ring
        have hmQ : ∀ i ∉ Q, (fun k => x k + (1/2) * (z k - x k)) i = 0 := by
          intro i hi; simp [hxoff i hi, hzQ.2.1 i hi]
        have h1 : φ (fun k => x k + (1/2) * (z k - x k)) ≤ φ z := hzQ.2.2 _ hmS hmQ
        have h3 : φ z ≤ φ x := hxQ.2.2 z hzQ.1 hzQ.2.1
        have e1 := hexp x (fun k => z k - x k) (1/2)
        have e2 := hexp x (fun k => z k - x k) 1
        have hz' : (fun k => x k + 1 * (z k - x k)) = z := by funext k; ring
        rw [hz'] at e2
        rw [e1] at h1
        rw [e2] at h3 h1
        nlinarith
      -- face matrix
      set A : Matrix Q Q ℝ := M.D.submatrix (fun i : Q => i.val) (fun i : Q => i.val) with hAdef
      have hA : A.PosDef := hD.submatrix Subtype.val_injective
      have hF : (M.faceF Q).PosDef := hA.inv
      have hFA : M.faceF Q * A = 1 :=
        Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
      have hsumF : 0 < ∑ i : Q, ∑ j : Q, M.faceF Q i j := by
        have hv : (fun _ : Q => (1:ℝ)) ≠ 0 := by
          obtain ⟨k, hk⟩ := hQne
          intro h; have := congrFun h ⟨k, hk⟩; simp at this
        have := hF.dotProduct_mulVec_pos hv
        simpa [dotProduct, Matrix.mulVec] using this
      refine ⟨hQne, hdem, hxz, hsumF, ?_⟩
      -- KKT
      set g : Fin n → ℝ := fun k => M.c k - p k - ∑ j, M.D k j * x j with hg
      have hdir : ∀ y ∈ productSimplex (Fin n), ∑ k, (y k - x k) * g k ≤ 0 := by
        intro y hy
        by_contra hpos; push Not at hpos
        set a := ∑ k, (y k - x k) * g k with ha
        set b := ∑ i, ∑ j, (y i - x i) * M.D i j * (y j - x j) with hb
        have hden : 0 < a + |b| + 1 := by positivity
        set t := a / (a + |b| + 1) with ht
        have ht0 : 0 < t := div_pos hpos hden
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith [abs_nonneg b]
        have hzS : (fun k => x k + t * (y k - x k)) ∈ productSimplex (Fin n) := by
          refine ⟨fun k => ?_, ?_⟩
          · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (hxnn k), mul_nonneg ht0.le (hy.1 k)]
          · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hxsum, hy.2]
            ring
        have hle := hxmax _ hzS
        rw [hexp] at hle
        have h5 : t * a ≤ t ^ 2 * b / 2 := by
          have : (fun k => y k - x k) = fun k => y k - x k := rfl
          linarith
        have h6 : a ≤ t * b / 2 := by
          have : t * a ≤ t * (t * b / 2) := by nlinarith
          exact le_of_mul_le_mul_left this ht0
        have h7 : t * |b| < a := by
          rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [abs_nonneg b]
        have h8 : t * b ≤ t * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) ht0.le
        linarith
      set S := ∑ j, x j * g j with hS
      have hgle : ∀ k, g k ≤ S := by
        intro k
        have hek : (fun j => if j = k then (1:ℝ) else 0) ∈ productSimplex (Fin n) := by
          refine ⟨fun j => ?_, ?_⟩
          · dsimp only; split_ifs <;> norm_num
          · simp
        have := hdir _ hek
        simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        linarith
      have hsum0 : ∑ k, x k * (S - g k) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hxsum]; ring
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        mul_nonneg (hxnn k) (sub_nonneg.2 (hgle k)))).mp hsum0
      have hgeq : ∀ k ∈ Q, g k = S := by
        intro k hk
        have h := hterm k (Finset.mem_univ k)
        have hxk := (hQmem k).mp hk
        rcases mul_eq_zero.mp h with h | h
        · linarith
        · linarith
      have hDx : ∀ k : Q, ∑ j, M.D k j * x j = ∑ j : Q, A k j * x j := by
        intro k
        have h : ∑ j : Q, A k j * x j = ∑ j ∈ Q, M.D k j * x j :=
          Finset.sum_coe_sort Q (fun j => M.D k j * x j)
        rw [h]
        symm
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro j _ hj; simp [hxoff j hj]
      set F := M.faceF Q with hFdef
      set xQ : Q → ℝ := fun i => x i with hxQdef
      set u : Q → ℝ := fun i => M.c i - p i with hudef
      have hAx : Matrix.mulVec A xQ = fun i => u i - S := by
        funext k
        have h := hgeq k k.2
        simp only [hg] at h
        have h2 := hDx k
        show ∑ j : Q, A k j * x j = M.c k - p k - S
        rw [← h2]; linarith
      have hxF : ∀ i : Q, x i = ∑ j, F i j * (u j - S) := by
        intro i
        have h : xQ = Matrix.mulVec F (Matrix.mulVec A xQ) := by rw [Matrix.mulVec_mulVec, hFA, Matrix.one_mulVec]
        have h2 := congrFun h i
        rw [hAx] at h2
        simpa [Matrix.mulVec, dotProduct] using h2
      have hsumQ : ∑ i : Q, x i = 1 := by
        rw [Finset.sum_coe_sort Q x, ← hxsum]
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro j _ hj; exact hxoff j hj
      have hS' : S = (∑ i, ∑ j, F i j * u j - 1) / ∑ i, ∑ j, F i j := by
        rw [eq_div_iff hsumF.ne']
        have h : ∑ i : Q, ∑ j : Q, F i j * (u j - S) = 1 := by
          rw [← hsumQ]; exact Finset.sum_congr rfl (fun i _ => (hxF i).symm)
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
        linear_combination -h
      intro i
      show x i = ∑ j : Q, F i j * (u j + (1 - ∑ i, ∑ j, F i j * u j) / ∑ i, ∑ j, F i j)
      rw [hxF i]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hS']
      field_simp
      ring
