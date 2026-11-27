-- Prove2me | solution 1 for SelfDualLP.Regularity.Supplement.theorem_2_i
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:42.171719+00:00
-- url     : https://prove2.me/submissions/c0b4a53b-9126-4a4d-84c8-f849ae446003

import Definitions.Def_SelfDualLP_Regularity_Supplement_HLD

open Matrix

open SelfDualLP
open SelfDualLP.Regularity
open SelfDualLP.Regularity.Supplement

open SelfDualLP.Regularity LinearOptimization

/-- **Theorem 2 (i)** (Ye–Todd–Mizuno 1994, p. 56). For arbitrary data `A, b, c` and initial
points `x⁰ > 0`, `s⁰ > 0`, `y⁰`, the linear-programming dual (HLD) of (HLP) is (HLP) in the
multipliers `(y′, x′, τ′, θ′)`:
1. the general-form encoding `hlpLP` is (HLP): reading `v` as `(y, x, τ, θ)` with slacks
   is injective, and its image of the feasible set of `hlpLP` is `Fₕ`; its cost is
   `((x⁰)ᵀs⁰ + 1)θ`;
2. the image of the feasible set of (HLD) is again `Fₕ`;
3. the raw dual objective `max pᵀ(0,0,0,−(x⁰)ᵀs⁰−1)` equals `−((x⁰)ᵀs⁰ + 1)θ′`, so the
   optimal solutions of the maximization (HLD) are exactly the optimal points of (HLP);
4. in the equivalent minimization form, (HLD) is literally the data of (HLP). -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ)
    (hx₀ : ∀ j, 0 < x₀ j) (hs₀ : ∀ j, 0 < s₀ j) :
    Function.Injective (toHLPPoint A b c x₀ y₀ s₀) ∧
    toHLPPoint A b c x₀ y₀ s₀ '' generalFeasibleSet (hlpLP A b c x₀ y₀ s₀) =
      {w | HLPFeasible A b c x₀ y₀ s₀ w} ∧
    (∀ v, (hlpLP A b c x₀ y₀ s₀).c ⬝ᵥ v = HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ v)) ∧
    toHLPPoint A b c x₀ y₀ s₀ '' generalFeasibleSet (HLD A b c x₀ y₀ s₀) =
      {w | HLPFeasible A b c x₀ y₀ s₀ w} ∧
    (∀ p, p ⬝ᵥ (hlpLP A b c x₀ y₀ s₀).b =
      -HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p)) ∧
    (∀ p, IsLpDualOptimal (hlpLP A b c x₀ y₀ s₀).b
        (generalFeasibleSet (HLD A b c x₀ y₀ s₀)) p ↔
      IsHLPOptimal A b c x₀ y₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p)) ∧
    HLD A b c x₀ y₀ s₀ = hlpLP A b c x₀ y₀ s₀ := by
      have hMv : ∀ (v : Fin (m + n + 2) → ℝ),
          (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) ∘ (hlpIdx m n) =
            Sum.elim (Sum.elim
              (fun i => (A *ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))) i
                  - v (hlpIdx m n (Sum.inr (Sum.inl 0))) * b i
                  + v (hlpIdx m n (Sum.inr (Sum.inr 0))) * bBar A b x₀ i)
              (fun j => -(Aᵀ *ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i))))) j
                  + v (hlpIdx m n (Sum.inr (Sum.inl 0))) * c j
                  - v (hlpIdx m n (Sum.inr (Sum.inr 0))) * cBar A c y₀ s₀ j))
            (Sum.elim
              (fun _ => b ⬝ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i))))
                  - c ⬝ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))
                  + zBar b c x₀ y₀ * v (hlpIdx m n (Sum.inr (Sum.inr 0))))
              (fun _ => -(bBar A b x₀ ⬝ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i)))))
                  + cBar A c y₀ s₀ ⬝ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))
                  - zBar b c x₀ y₀ * v (hlpIdx m n (Sum.inr (Sum.inl 0))))) := by
        intro v
        rw [hlpMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
        ext k
        rcases k with (i | j) | (t | t)
        all_goals simp [fromBlocks_mulVec, Function.comp_def, mulVec, dotProduct, neg_mul,
          Finset.sum_neg_distrib]
        all_goals ring
      have h1 : ∀ v i, hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inl (Sum.inl i))) ⬝ᵥ v =
          (A *ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))) i
                  - v (hlpIdx m n (Sum.inr (Sum.inl 0))) * b i
                  + v (hlpIdx m n (Sum.inr (Sum.inr 0))) * bBar A b x₀ i :=
        fun v i => congrFun (hMv v) (Sum.inl (Sum.inl i))
      have h2 : ∀ v j, hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inl (Sum.inr j))) ⬝ᵥ v =
          -(Aᵀ *ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i))))) j
                  + v (hlpIdx m n (Sum.inr (Sum.inl 0))) * c j
                  - v (hlpIdx m n (Sum.inr (Sum.inr 0))) * cBar A c y₀ s₀ j :=
        fun v j => congrFun (hMv v) (Sum.inl (Sum.inr j))
      have h3 : ∀ v, hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inr (Sum.inl 0))) ⬝ᵥ v =
          b ⬝ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i))))
                  - c ⬝ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))
                  + zBar b c x₀ y₀ * v (hlpIdx m n (Sum.inr (Sum.inr 0))) :=
        fun v => congrFun (hMv v) (Sum.inr (Sum.inl 0))
      have h4 : ∀ v, hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inr (Sum.inr 0))) ⬝ᵥ v =
          -(bBar A b x₀ ⬝ᵥ (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i)))))
                  + cBar A c y₀ s₀ ⬝ᵥ (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j))))
                  - zBar b c x₀ y₀ * v (hlpIdx m n (Sum.inr (Sum.inl 0))) :=
        fun v => congrFun (hMv v) (Sum.inr (Sum.inr 0))
      have hfeas : ∀ v, v ∈ generalFeasibleSet (hlpLP A b c x₀ y₀ s₀) ↔
          HLPFeasible A b c x₀ y₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ v) := by
        intro v
        simp only [generalFeasibleSet, Set.mem_ofPred_eq, HLPFeasible, toHLPPoint]
        constructor
        · rintro ⟨hr, hc⟩
          have r1 := fun i => hr (hlpIdx m n (Sum.inl (Sum.inl i)))
          have r2 := fun j => hr (hlpIdx m n (Sum.inl (Sum.inr j)))
          have r3 := hr (hlpIdx m n (Sum.inr (Sum.inl 0)))
          have r4 := hr (hlpIdx m n (Sum.inr (Sum.inr 0)))
          have c2 := fun j => hc (hlpIdx m n (Sum.inl (Sum.inr j)))
          have c3 := hc (hlpIdx m n (Sum.inr (Sum.inl 0)))
          simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
            LinearConstraint.IsSatisfiedAt, VarSign.IsSatisfiedBy] at r1 r2 r3 r4 c2 c3
          refine ⟨?_, ?_, ?_, ?_, c2, c3, fun j => r2 j, r3⟩
          · ext i
            have := r1 i
            rw [h1] at this
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            linarith
          · ext j
            have := h2 v j
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
            rw [show (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inl (Sum.inr j))) =
              hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inl (Sum.inr j))) ⬝ᵥ v from rfl, this]
          · rw [show (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inr (Sum.inl 0))) =
              hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inr (Sum.inl 0))) ⬝ᵥ v from rfl, h3]
          · rw [h4] at r4
            exact r4
        · rintro ⟨e1, e2, e3, e4, hx, hτ, hs, hκ⟩
          refine ⟨fun r => ?_, fun r => ?_⟩
          · obtain ⟨k, rfl⟩ := (hlpIdx m n).surjective r
            rcases k with (i | j) | (t | t)
            · simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                LinearConstraint.IsSatisfiedAt]
              rw [h1]
              have := congrFun e1 i
              simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
                Pi.zero_apply] at this
              linarith
            · simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                LinearConstraint.IsSatisfiedAt]
              exact hs j
            · obtain rfl : t = 0 := Subsingleton.elim _ _
              simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                LinearConstraint.IsSatisfiedAt]
              exact hκ
            · obtain rfl : t = 0 := Subsingleton.elim _ _
              simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                LinearConstraint.IsSatisfiedAt]
              rw [h4]
              exact e4
          · obtain ⟨k, rfl⟩ := (hlpIdx m n).surjective r
            rcases k with (i | j) | (t | t)
            · simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                VarSign.IsSatisfiedBy]
            · simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                VarSign.IsSatisfiedBy]
              exact hx j
            · obtain rfl : t = 0 := Subsingleton.elim _ _
              simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                VarSign.IsSatisfiedBy]
              exact hτ
            · simp only [hlpLP, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
                VarSign.IsSatisfiedBy]
      have hinj : Function.Injective (toHLPPoint A b c x₀ y₀ s₀) := by
        intro v w h
        have hy := congrArg HLPPoint.y h
        have hx := congrArg HLPPoint.x h
        have hτ := congrArg HLPPoint.τ h
        have hθ := congrArg HLPPoint.θ h
        simp only [toHLPPoint] at hy hx hτ hθ
        funext r
        obtain ⟨k, rfl⟩ := (hlpIdx m n).surjective r
        rcases k with (i | j) | (t | t)
        · exact congrFun hy i
        · exact congrFun hx j
        · obtain rfl : t = 0 := Subsingleton.elim _ _
          exact hτ
        · obtain rfl : t = 0 := Subsingleton.elim _ _
          exact hθ
      have himg : toHLPPoint A b c x₀ y₀ s₀ '' generalFeasibleSet (hlpLP A b c x₀ y₀ s₀) =
          {w | HLPFeasible A b c x₀ y₀ s₀ w} := by
        ext w
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact (hfeas v).1 hv
        · intro hw
          obtain ⟨y, x, τ, θ, s, κ⟩ := w
          obtain ⟨e1, e2, e3, e4, -⟩ := id hw
          simp only at e1 e2 e3 e4
          obtain ⟨v, hv⟩ : ∃ v : Fin (m + n + 2) → ℝ, v = fun r =>
              Sum.elim (Sum.elim y x) (Sum.elim (fun _ => τ) (fun _ => θ)) ((hlpIdx m n).symm r) :=
            ⟨_, rfl⟩
          have hy' : (fun i => v (hlpIdx m n (Sum.inl (Sum.inl i)))) = y := by
            funext i; rw [hv]; simp
          have hx' : (fun j => v (hlpIdx m n (Sum.inl (Sum.inr j)))) = x := by
            funext j; rw [hv]; simp
          have hτ' : v (hlpIdx m n (Sum.inr (Sum.inl 0))) = τ := by
            rw [hv]; simp
          have hθ' : v (hlpIdx m n (Sum.inr (Sum.inr 0))) = θ := by
            rw [hv]; simp
          have hs' : (fun j => (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inl (Sum.inr j))))
              = s := by
            rw [e2]
            funext j
            rw [show (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inl (Sum.inr j))) =
              hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inl (Sum.inr j))) ⬝ᵥ v from rfl, h2,
              hy', hτ', hθ']
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
          have hκ' : (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inr (Sum.inl 0))) = κ := by
            rw [e3]
            rw [show (hlpMatrix A b c x₀ y₀ s₀ *ᵥ v) (hlpIdx m n (Sum.inr (Sum.inl 0))) =
              hlpMatrix A b c x₀ y₀ s₀ (hlpIdx m n (Sum.inr (Sum.inl 0))) ⬝ᵥ v from rfl, h3,
              hy', hx', hθ']
          have hTv : toHLPPoint A b c x₀ y₀ s₀ v = ⟨y, x, τ, θ, s, κ⟩ := by
            simp only [toHLPPoint]
            rw [hy', hx', hτ', hθ', hs', hκ']
          refine ⟨v, (hfeas v).2 ?_, hTv⟩
          rw [hTv]
          exact hw
      have hobj : ∀ v, (hlpLP A b c x₀ y₀ s₀).c ⬝ᵥ v =
          HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ v) := by
        intro v
        rw [dotProduct, ← Equiv.sum_comp (hlpIdx m n)]
        simp [hlpLP, Fintype.sum_sum_type, HLPObjective, toHLPPoint]
      have hdb : ∀ p, p ⬝ᵥ (hlpLP A b c x₀ y₀ s₀).b =
          -HLPObjective x₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p) := by
        intro p
        rw [dotProduct, ← Equiv.sum_comp (hlpIdx m n)]
        simp [hlpLP, Fintype.sum_sum_type, HLPObjective, toHLPPoint]
        ring
      have hHLD : HLD A b c x₀ y₀ s₀ = hlpLP A b c x₀ y₀ s₀ := by
        have hA : -(hlpLP A b c x₀ y₀ s₀).Aᵀ = (hlpLP A b c x₀ y₀ s₀).A := by
          ext r s
          simp only [hlpLP, Matrix.neg_apply, transpose_apply, hlpMatrix, reindex_apply,
            submatrix_apply]
          generalize (hlpIdx m n).symm r = k
          generalize (hlpIdx m n).symm s = l
          rcases k with (i | j) | (t | t) <;> rcases l with (i' | j') | (t' | t') <;>
            simp [fromBlocks]
        have hb : -(hlpLP A b c x₀ y₀ s₀).c = (hlpLP A b c x₀ y₀ s₀).b := by
          funext r
          simp only [hlpLP, Pi.neg_apply]
          generalize (hlpIdx m n).symm r = k
          rcases k with (i | j) | (t | t) <;> simp <;> ring
        have hc : -(hlpLP A b c x₀ y₀ s₀).b = (hlpLP A b c x₀ y₀ s₀).c := by
          rw [← hb, neg_neg]
        have hrow : (fun j => ((hlpLP A b c x₀ y₀ s₀).colSign j).dualRel) =
            (hlpLP A b c x₀ y₀ s₀).rowRel := by
          funext r
          simp only [hlpLP]
          generalize (hlpIdx m n).symm r = k
          rcases k with (i | j) | (t | t) <;> rfl
        have hcol : (fun i => ((hlpLP A b c x₀ y₀ s₀).rowRel i).dualSign) =
            (hlpLP A b c x₀ y₀ s₀).colSign := by
          funext r
          simp only [hlpLP]
          generalize (hlpIdx m n).symm r = k
          rcases k with (i | j) | (t | t) <;> rfl
        unfold HLD dualLP
        rw [hA, hb, hc, hrow, hcol]
      have hopt : ∀ p, IsLpDualOptimal (hlpLP A b c x₀ y₀ s₀).b
            (generalFeasibleSet (HLD A b c x₀ y₀ s₀)) p ↔
          IsHLPOptimal A b c x₀ y₀ s₀ (toHLPPoint A b c x₀ y₀ s₀ p) := by
        intro p
        rw [hHLD]
        unfold IsLpDualOptimal IsHLPOptimal
        rw [hfeas]
        constructor
        · rintro ⟨hp, hq⟩
          refine ⟨hp, fun w hw => ?_⟩
          obtain ⟨q, hq', rfl⟩ : w ∈ toHLPPoint A b c x₀ y₀ s₀ ''
              generalFeasibleSet (hlpLP A b c x₀ y₀ s₀) := by
            rw [himg]; exact hw
          have := hq q hq'
          rw [hdb, hdb] at this
          linarith
        · rintro ⟨hp, hq⟩
          refine ⟨hp, fun q hq' => ?_⟩
          have := hq (toHLPPoint A b c x₀ y₀ s₀ q) ((hfeas q).1 hq')
          rw [hdb, hdb]
          linarith
      exact ⟨hinj, himg, hobj, by rw [hHLD]; exact himg, hdb, hopt, hHLD⟩
