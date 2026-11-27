-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.Supplement.theorem_3_claim
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:06.625902+00:00
-- url     : https://prove2.me/submissions/5835dab4-7412-46a4-be4c-07655a843c2f

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

open TwoStageSRO
open TwoStageSRO.AsymOpt
open TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 49, Claim in the
proof of Theorem 3: let `T ⊆ Ξ` be a nonempty polyhedron, `ϵ̄ > 0`, `λ ∈ (0, 1)`, and let `ϵ` be the
radius of Theorem 3. For each `k ∈ {dim̲(T), …, dim(T)}` put `α_k = (2θ^T_Ξ / λ)^{dim(T) − k}`. Then for
each `F ∈ Faces(T)` with `dim(F) = k` and each `ζ̂ ∈ F` there is `ζ̄ ∈ F` with
`B(ζ̂, α_k ϵ) ∩ Ξ ⊆ {λζ + (1 − λ)ζ̄ : ζ ∈ B(ζ̄, ϵ̄) ∩ Ξ}` (54).

**Formalization Note** `ϵ` is `epsThm3 M p T εbar lam` and `α_k` is `alphaClaim M p T lam k`, so the
setting (`T`, `ϵ̄`, `λ`) is that of Theorem 3 (p. 48). The standing normalization `‖gᵢ‖_* = 1` (p. 33) is
`hG`; minimality of the representation of `Ξ` is not imposed (a disclosed strengthening). -/
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty)
    (εbar : ℝ) (hεbar : 0 < εbar) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ k : ℕ, minFaceDim T ≤ k → k ≤ polyDim T →
      ∀ F, IsFaceOf T F → polyDim F = k →
        ∀ zhat ∈ F, ∃ zbar ∈ F,
          ball p zhat (alphaClaim M p T lam k * epsThm3 M p T εbar lam) ∩ Xi M ⊆
            (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by
              obtain ⟨hl0, hl1⟩ := hlam
              have holder : ∀ (i : Fin mt) (u : Fin d → ℝ), u ⬝ᵥ M.G i ≤ ‖WithLp.toLp p u‖ := by
                intro i u
                have hbdd : BddAbove ((fun u => u ⬝ᵥ M.G i) '' {u : Fin d → ℝ | ‖WithLp.toLp p u‖ ≤ 1}) := by
                  by_contra h
                  have := hG i
                  unfold dualNorm at this
                  rw [Real.sSup_of_not_bddAbove h] at this
                  norm_num at this
                by_cases hu : u = 0
                · subst hu; simp
                have hpos : 0 < ‖WithLp.toLp p u‖ := by
                  rw [norm_pos_iff]; intro h; apply hu
                  simpa using congrArg (WithLp.ofLp) h
                set c := ‖WithLp.toLp p u‖ with hc
                have hmem : (c⁻¹ • u) ⬝ᵥ M.G i ≤ dualNorm p (M.G i) := by
                  apply le_csSup hbdd
                  refine ⟨c⁻¹ • u, ?_, rfl⟩
                  show ‖WithLp.toLp p (c⁻¹ • u)‖ ≤ 1
                  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
                  rw [inv_mul_cancel₀ hpos.ne']
                rw [hG i, smul_dotProduct, smul_eq_mul] at hmem
                have := mul_le_mul_of_nonneg_left hmem hpos.le
                rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at this
                exact this
              have reduce : ∀ (zc : Fin d → ℝ) (R : ℝ) (zbar : Fin d → ℝ), zbar ∈ Xi M →
                  (∀ ζ ∈ ball p zc R ∩ Xi M, ‖WithLp.toLp p (ζ - zbar)‖ ≤ lam * εbar ∧
                    ∀ i, (M.G *ᵥ zbar) i = M.g0 i ∨
                      ‖WithLp.toLp p (ζ - zbar)‖ ≤ lam * ((M.G *ᵥ zbar) i - M.g0 i)) →
                  ball p zc R ∩ Xi M ⊆
                    (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by
                intro zc R zbar hzbar H ζ hζ
                obtain ⟨h1, h2⟩ := H ζ hζ
                refine ⟨zbar + lam⁻¹ • (ζ - zbar), ⟨?_, ?_⟩, ?_⟩
                · show ‖WithLp.toLp p (zbar + lam⁻¹ • (ζ - zbar) - zbar)‖ ≤ εbar
                  rw [add_sub_cancel_left, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
                    abs_inv, abs_of_pos hl0]
                  rw [inv_mul_le_iff₀ hl0]; exact h1
                · intro i
                  have hζX : M.g0 i ≤ (M.G *ᵥ ζ) i := hζ.2 i
                  have hzX : M.g0 i ≤ (M.G *ᵥ zbar) i := hzbar i
                  have hlin : (M.G *ᵥ (zbar + lam⁻¹ • (ζ - zbar))) i =
                      (M.G *ᵥ zbar) i + lam⁻¹ * ((M.G *ᵥ ζ) i - (M.G *ᵥ zbar) i) := by
                    simp [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
                  show M.g0 i ≤ (M.G *ᵥ (zbar + lam⁻¹ • (ζ - zbar))) i
                  rw [hlin]
                  have hh : (M.G *ᵥ zbar) i - (M.G *ᵥ ζ) i ≤ ‖WithLp.toLp p (ζ - zbar)‖ := by
                    have := holder i (zbar - ζ)
                    have e : (zbar - ζ) ⬝ᵥ M.G i = (M.G *ᵥ zbar) i - (M.G *ᵥ ζ) i := by
                      simp only [Matrix.mulVec, dotProduct_comm _ zbar, dotProduct_comm _ ζ, sub_dotProduct]
                    rw [e] at this
                    have e2 : WithLp.toLp p (zbar - ζ) = -WithLp.toLp p (ζ - zbar) := by
                      rw [← WithLp.toLp_neg, neg_sub]
                    rw [e2, norm_neg] at this
                    exact this
                  rcases h2 i with h | h
                  · rw [h]
                    have : 0 ≤ lam⁻¹ * ((M.G *ᵥ ζ) i - M.g0 i) :=
                      mul_nonneg (inv_nonneg.mpr hl0.le) (by linarith)
                    linarith
                  · have : (1 - lam) * ((M.G *ᵥ zbar) i - M.g0 i) ≤ (M.G *ᵥ ζ) i - M.g0 i := by nlinarith
                    have key : -((M.G *ᵥ zbar) i - M.g0 i) * lam ≤ ((M.G *ᵥ ζ) i - (M.G *ᵥ zbar) i) := by
                      nlinarith
                    have : lam⁻¹ * ((M.G *ᵥ ζ) i - (M.G *ᵥ zbar) i) ≥ -((M.G *ᵥ zbar) i - M.g0 i) := by
                      rw [ge_iff_le, le_inv_mul_iff₀ hl0]; linarith
                    linarith
                · show lam • (zbar + lam⁻¹ • (ζ - zbar)) + (1 - lam) • zbar = ζ
                  rw [smul_add, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
                  module
              have hrow : ∀ (i : Fin mt) (ζ : Fin d → ℝ), (M.G *ᵥ ζ) i = M.G i ⬝ᵥ ζ := fun i ζ => rfl
              have vs_ker : ∀ (S : Set (Fin d → ℝ)) (w : Fin d → ℝ) (t : ℝ), S ⊆ {x | w ⬝ᵥ x = t} →
                  ∀ v ∈ vectorSpan ℝ S, w ⬝ᵥ v = 0 := by
                intro S w t hS v hv
                rw [vectorSpan_def] at hv
                induction hv using Submodule.span_induction with
                | mem x hx =>
                  obtain ⟨a, ha, b, hb, rfl⟩ := hx
                  have h1 := hS ha; have h2 := hS hb
                  simp only [Set.mem_ofPred_eq] at h1 h2
                  show w ⬝ᵥ (a - b) = 0
                  rw [dotProduct_sub, h1, h2, sub_self]
                | zero => simp
                | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
                | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
              have dimdrop : ∀ (F : Set (Fin d → ℝ)) (i : Fin mt), (F ∩ hyperplane M i).Nonempty →
                  ¬ F ⊆ hyperplane M i → polyDim (F ∩ hyperplane M i) < polyDim F := by
                intro F i ⟨y, hyF, hyH⟩ hnot
                obtain ⟨x, hxF, hxH⟩ := Set.not_subset.mp hnot
                unfold polyDim
                apply Submodule.finrank_lt_finrank_of_lt
                refine lt_of_le_of_ne (vectorSpan_mono ℝ Set.inter_subset_left) ?_
                intro heq
                have hmem : x -ᵥ y ∈ vectorSpan ℝ F := vsub_mem_vectorSpan ℝ hxF hyF
                rw [← heq] at hmem
                have := vs_ker _ (M.G i) (M.g0 i) (fun z hz => hz.2) _ hmem
                apply hxH
                show (M.G *ᵥ x) i = M.g0 i
                have hy' : M.G i ⬝ᵥ y = M.g0 i := hyH
                rw [hrow]
                have : M.G i ⬝ᵥ (x - y) = 0 := this
                rw [dotProduct_sub, hy'] at this
                linarith
              have hGne : ∀ i, M.G i ≠ 0 := by
                intro i h
                have := hG i
                rw [h] at this
                unfold dualNorm at this
                have e : ((fun u => u ⬝ᵥ (0 : Fin d → ℝ)) '' {u : Fin d → ℝ | ‖WithLp.toLp p u‖ ≤ 1}) = {0} := by
                  ext x; simp only [dotProduct_zero, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                  constructor
                  · rintro ⟨u, _, rfl⟩; rfl
                  · rintro rfl; exact ⟨0, by simp, rfl⟩
                rw [e, csSup_singleton] at this
                norm_num at this
              have faceT : ∀ i, (T ∩ hyperplane M i).Nonempty → IsFaceOf T (T ∩ hyperplane M i) := by
                intro i hne
                refine ⟨hne, Or.inr (Or.inr ⟨-M.G i, -M.g0 i, ⟨neg_ne_zero.mpr (hGne i), ?_, ?_⟩, ?_⟩)⟩
                · intro x hx
                  have := hTXi hx i
                  simp only [Set.mem_ofPred_eq, neg_dotProduct]
                  rw [hrow] at this; linarith
                · obtain ⟨y, hyT, hyH⟩ := hne
                  refine ⟨y, hyT, ?_⟩
                  simp only [Set.mem_ofPred_eq, neg_dotProduct, neg_inj]
                  exact hyH
                · ext x
                  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, neg_dotProduct, neg_inj, hyperplane, hrow]
              have faceInter : ∀ F, IsFaceOf T F → ∀ i, (F ∩ hyperplane M i).Nonempty →
                  IsFaceOf T (F ∩ hyperplane M i) := by
                intro F hF i hne
                rcases hF.2 with h | h | ⟨w, t, ⟨hw0, hval, hsup⟩, rfl⟩
                · subst h; simp at hne
                · subst h; exact faceT i hne
                · obtain ⟨y, ⟨hyT, hyw⟩, hyH⟩ := hne
                  have hyw' : w ⬝ᵥ y = t := hyw
                  have hyH' : M.G i ⬝ᵥ y = M.g0 i := hyH
                  by_cases hw' : w - M.G i = 0
                  · have hw : w = M.G i := sub_eq_zero.mp hw'
                    have ht : t = M.g0 i := by rw [← hyw', ← hyH', hw]
                    have e : T ∩ {x | w ⬝ᵥ x = t} ∩ hyperplane M i = T ∩ hyperplane M i := by
                      ext x
                      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hyperplane, hrow, hw, ht]
                      tauto
                    rw [e]; exact faceT i ⟨y, hyT, hyH⟩
                  · refine ⟨⟨y, ⟨hyT, hyw⟩, hyH⟩, Or.inr (Or.inr ⟨w - M.G i, t - M.g0 i, ⟨hw', ?_, ?_⟩, ?_⟩)⟩
                    · intro x hx
                      have h1 := hTXi hx i
                      have h2 : w ⬝ᵥ x ≤ t := hval hx
                      rw [hrow] at h1
                      simp only [Set.mem_ofPred_eq, sub_dotProduct]; linarith
                    · refine ⟨y, hyT, ?_⟩
                      simp only [Set.mem_ofPred_eq, sub_dotProduct, hyw', hyH']
                    · ext x
                      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hyperplane, hrow, sub_dotProduct]
                      constructor
                      · rintro ⟨⟨hxT, h1⟩, h2⟩; exact ⟨hxT, by rw [h1, h2]⟩
                      · rintro ⟨hxT, h⟩
                        have h1 := hTXi hxT i
                        have h2 : w ⬝ᵥ x ≤ t := hval hxT
                        rw [hrow] at h1
                        exact ⟨⟨hxT, by linarith⟩, by linarith⟩
              have faceSub : ∀ F, IsFaceOf T F → F ⊆ T := by
                intro F hF
                rcases hF.2 with h | h | ⟨w, t, _, rfl⟩
                · rw [h]; exact Set.empty_subset _
                · rw [h]
                · exact Set.inter_subset_left
              have subdim : ∀ G G', IsFaceOf T G → IsFaceOf T G' → G' ⊆ G → G' ≠ G →
                  polyDim G' < polyDim G := by
                intro G G' hG hG' hsub hne
                obtain ⟨y, hy⟩ := hG'.1
                rcases hG'.2 with h | h | ⟨w, t, ⟨_, _, _⟩, hG'eq⟩
                · rw [h] at hy; exact absurd hy (Set.notMem_empty _)
                · exact absurd (Set.Subset.antisymm (faceSub G hG) (h ▸ hsub)) (by
                    intro h2; exact hne (h.trans h2.symm))
                · have hx : ∃ x ∈ G, x ∉ G' := by
                    by_contra hc; push Not at hc; exact hne (Set.Subset.antisymm hsub hc)
                  obtain ⟨x, hxG, hxG'⟩ := hx
                  unfold polyDim
                  apply Submodule.finrank_lt_finrank_of_lt
                  refine lt_of_le_of_ne (vectorSpan_mono ℝ hsub) ?_
                  intro heq
                  have hmem : x -ᵥ y ∈ vectorSpan ℝ G := vsub_mem_vectorSpan ℝ hxG (hsub hy)
                  rw [← heq] at hmem
                  have hS : G' ⊆ {z | w ⬝ᵥ z = t} := by rw [hG'eq]; exact Set.inter_subset_right
                  have h0 := vs_ker _ w t hS _ hmem
                  have hyt : w ⬝ᵥ y = t := hS hy
                  have : w ⬝ᵥ (x - y) = 0 := h0
                  rw [dotProduct_sub, hyt] at this
                  apply hxG'
                  rw [hG'eq]
                  exact ⟨faceSub G hG hxG, show w ⬝ᵥ x = t by linarith⟩
              have hmin : ∀ G, IsFaceOf T G → minFaceDim T ≤ polyDim G := by
                intro G
                induction h : polyDim G using Nat.strong_induction_on generalizing G with
                | _ j IH =>
                  intro hG
                  by_cases hm : IsMinimalFaceOf T G
                  · exact Nat.sInf_le ⟨G, hm, h⟩
                  · unfold IsMinimalFaceOf at hm
                    push Not at hm
                    obtain ⟨G', hG', hsub, hne⟩ := hm hG
                    have := subdim G G' hG hG' hsub hne
                    rw [h] at this
                    exact (IH _ this G' rfl hG').trans this.le
              have distH : ∀ (i : Fin mt) (ζ : Fin d → ℝ), 0 ≤ (M.G *ᵥ ζ) i - M.g0 i →
                  ptDist p ζ (hyperplane M i) ≤ (((M.G *ᵥ ζ) i - M.g0 i : ℝ) : EReal) := by
                intro i ζ hs
                set s := (M.G *ᵥ ζ) i - M.g0 i with hsdef
                apply le_of_forall_gt_imp_ge_of_dense
                intro c hc
                induction c using EReal.rec with
                | bot => exact absurd hc (not_lt_bot)
                | top => exact le_top
                | coe c =>
                  rw [EReal.coe_lt_coe_iff] at hc
                  have hc0 : 0 < c := lt_of_le_of_lt hs hc
                  have hlt : s / c < dualNorm p (M.G i) := by
                    rw [hG i, div_lt_one hc0]; exact hc
                  obtain ⟨_, ⟨u, hu, rfl⟩, hua⟩ := exists_lt_of_lt_csSup
                    (⟨0, 0, by simp, by simp⟩ : ((fun u => u ⬝ᵥ M.G i) '' {u : Fin d → ℝ | ‖WithLp.toLp p u‖ ≤ 1}).Nonempty) hlt
                  set a := u ⬝ᵥ M.G i with ha
                  have ha0 : 0 < a := lt_of_le_of_lt (div_nonneg hs hc0.le) hua
                  have hz' : ζ - (s / a) • u ∈ hyperplane M i := by
                    show (M.G *ᵥ (ζ - (s / a) • u)) i = M.g0 i
                    rw [hrow, dotProduct_sub, dotProduct_smul, dotProduct_comm (M.G i) u, ← ha, ← hrow,
                      smul_eq_mul, div_mul_cancel₀ _ ha0.ne']
                    rw [hsdef]; ring
                  unfold ptDist
                  refine (iInf₂_le _ hz').trans ?_
                  rw [EReal.coe_le_coe_iff, sub_sub_cancel, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
                    abs_of_nonneg (div_nonneg hs ha0.le)]
                  have hu' : ‖WithLp.toLp p u‖ ≤ 1 := hu
                  have h1 : s / a ≤ c := by
                    rw [div_le_iff₀ ha0]; rw [div_lt_iff₀ hc0] at hua; linarith
                  calc s / a * ‖WithLp.toLp p u‖ ≤ s / a * 1 :=
                        mul_le_mul_of_nonneg_left hu' (div_nonneg hs ha0.le)
                    _ ≤ c := by rw [mul_one]; exact h1
              have rho0 : ∀ S, 0 ≤ rho1 M p S := by
                intro S; unfold rho1; refine le_iInf₂ (fun i _ => ?_); unfold setDist
                exact le_iInf₂ (fun _ _ => le_iInf₂ (fun _ _ => EReal.coe_nonneg.mpr (norm_nonneg _)))
              have rad0 : ∀ k S, 0 ≤ radiusAux M p k S := by
                intro k
                induction k with
                | zero => intro S; exact rho0 S
                | succ k ih => intro S; simp only [radiusAux]; exact le_min (rho0 S) (le_iInf₂ fun F _ => ih F)
              obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (min (εbar : EReal) (polyRadius M p T)).toReal := ⟨_, rfl⟩
              have hmin0 : 0 ≤ min (εbar : EReal) (polyRadius M p T) :=
                le_min (EReal.coe_nonneg.mpr hεbar.le) (rad0 _ _)
              have hδ0 : 0 ≤ δ := by rw [hδ]; exact EReal.toReal_nonneg hmin0
              have hδε : δ ≤ εbar := by
                rw [hδ]
                have := EReal.toReal_le_toReal (min_le_left (εbar : EReal) (polyRadius M p T))
                  (ne_bot_of_le_ne_bot (by simp) hmin0) (EReal.coe_ne_top _)
                simpa using this
              classical
              have strictPoint : ∀ (q : ℕ) (A : Fin q → Fin d → ℝ) (b : Fin q → ℝ)
                  (S : Set (Fin d → ℝ)), S.Nonempty →
                  (∀ x ∈ S, ∀ y ∈ S, (1 / 2 : ℝ) • (x + y) ∈ S) →
                  (∀ x ∈ S, ∀ i, A i ⬝ᵥ x ≤ b i) →
                  ∀ J : Finset (Fin q), (∀ i ∈ J, ∃ x ∈ S, A i ⬝ᵥ x < b i) →
                  ∃ x ∈ S, ∀ i ∈ J, A i ⬝ᵥ x < b i := by
                intro q A b S hne hmid hle J
                induction J using Finset.induction_on with
                | empty => intro _; obtain ⟨x, hx⟩ := hne; exact ⟨x, hx, by simp⟩
                | @insert i J hi IH =>
                  intro H
                  obtain ⟨x, hx, hxlt⟩ := IH (fun j hj => H j (Finset.mem_insert_of_mem hj))
                  obtain ⟨y, hy, hylt⟩ := H i (Finset.mem_insert_self _ _)
                  refine ⟨(1 / 2 : ℝ) • (x + y), hmid x hx y hy, ?_⟩
                  intro j hj
                  rw [dotProduct_smul, dotProduct_add, smul_eq_mul]
                  rcases Finset.mem_insert.mp hj with rfl | hj
                  · have := hle x hx j; linarith
                  · have := hxlt j hj; have := hle y hy j; linarith
              have smallStep : ∀ (q : ℕ) (A : Fin q → Fin d → ℝ) (b : Fin q → ℝ)
                  (J : Finset (Fin q)) (x v : Fin d → ℝ),
                  (∀ i ∈ J, A i ⬝ᵥ x < b i ∨ A i ⬝ᵥ v = 0 ∧ A i ⬝ᵥ x ≤ b i) →
                  ∃ t : ℝ, 0 < t ∧ ∀ i ∈ J, A i ⬝ᵥ (x + t • v) ≤ b i := by
                intro q A b J x v H
                have hev : ∀ᶠ t : ℝ in nhds 0, ∀ i ∈ J, A i ⬝ᵥ (x + t • v) ≤ b i := by
                  apply (Filter.eventually_all_finset J).mpr
                  intro i hi
                  rcases H i hi with h | ⟨h, hx⟩
                  · have hc : Continuous (fun t : ℝ => A i ⬝ᵥ (x + t • v)) := by
                      fun_prop
                    have hh : Set.Iio (b i) ∈ nhds (A i ⬝ᵥ (x + (0 : ℝ) • v)) :=
                      isOpen_Iio.mem_nhds (by simpa using h)
                    have he := hc.continuousAt.preimage_mem_nhds hh
                    filter_upwards [he] with t ht using le_of_lt ht
                  · filter_upwards [] with t
                    simpa [dotProduct_add, dotProduct_smul, h] using hx
                obtain ⟨e, he, heall⟩ := Metric.eventually_nhds_iff.mp hev
                refine ⟨e / 2, by linarith, heall ?_⟩
                rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < e / 2)]
                linarith
              have facetExtension : ∀ (S F : Set (Fin d → ℝ)),
                  CombOpt.MatchingPolytope.IsPolyhedron S → IsFaceOf S F → F ≠ S →
                  ∃ G, IsFacetOf S G ∧ F ⊆ G := by
                intro S F hSp hF hFS
                obtain ⟨q, A, b, hS⟩ := hSp
                have hle : ∀ x ∈ S, ∀ i, A i ⬝ᵥ x ≤ b i := by
                  intro x hx; rw [hS] at hx; exact hx
                have hsub : F ⊆ S := by
                  rcases hF.2 with h | h | ⟨w,t,_,rfl⟩
                  · rw [h]; exact Set.empty_subset _
                  · rw [h]
                  · exact Set.inter_subset_left
                have hSne : S.Nonempty := hF.1.mono hsub
                have hmidS : ∀ x ∈ S, ∀ y ∈ S, (1/2:ℝ) • (x+y) ∈ S := by
                  intro x hx y hy; rw [hS]
                  intro i; simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]
                  have := hle x hx i; have := hle y hy i; linarith
                rcases hF.2 with h | h | ⟨w,t,⟨hw0,hwle,hwt⟩,hFeq⟩
                · exact False.elim (by simpa [h] using hF.1)
                · exact False.elim (hFS h)
                have hmidF : ∀ x ∈ F, ∀ y ∈ F, (1/2:ℝ) • (x+y) ∈ F := by
                  intro x hx y hy
                  have hxw : w ⬝ᵥ x = t := (hFeq ▸ hx).2
                  have hyw : w ⬝ᵥ y = t := (hFeq ▸ hy).2
                  rw [hFeq]; refine ⟨hmidS x (hsub hx) y (hsub hy), ?_⟩
                  show w ⬝ᵥ ((1/2:ℝ) • (x+y)) = t
                  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]; linarith
                let E : Finset (Fin q) := Finset.univ.filter (fun i => ∀ x ∈ S, A i ⬝ᵥ x = b i)
                have hE : ∀ i, i ∈ E ↔ ∀ x ∈ S, A i ⬝ᵥ x = b i := by simp [E]
                let P : Finset (Fin q) → Prop := fun J =>
                  (∀ i ∈ J, i ∉ E) ∧ ∀ x, x ∈ S ↔
                    (∀ i ∈ E, A i ⬝ᵥ x = b i) ∧ (∀ i ∈ J, A i ⬝ᵥ x ≤ b i)
                have hP : ∃ J, P J := by
                  refine ⟨Finset.univ \ E, ?_, ?_⟩
                  · simp
                  · intro x; constructor
                    · intro hx; exact ⟨fun i hi => (hE i).mp hi x hx, fun i _ => hle x hx i⟩
                    · rintro ⟨he,hj⟩; rw [hS]; intro i
                      by_cases hi : i ∈ E
                      · exact (he i hi).le
                      · exact hj i (by simp [hi])
                obtain ⟨J, hJP, hJmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card hP
                have hJnot : ∀ i ∈ J, i ∉ E := hJP.1
                have hrep := hJP.2
                have hstrict : ∀ i ∈ J, ∃ x ∈ S, A i ⬝ᵥ x < b i := by
                  intro i hi
                  have h := hJnot i hi
                  rw [hE] at h
                  push Not at h
                  obtain ⟨x,hx,hne⟩ := h
                  exact ⟨x,hx,lt_of_le_of_ne (hle x hx i) hne⟩
                obtain ⟨x,hx,hxlt⟩ := strictPoint q A b S hSne hmidS hle J hstrict
                have hjF : ∃ j ∈ J, ∀ u ∈ F, A j ⬝ᵥ u = b j := by
                  by_contra h
                  push Not at h
                  have hstrictF : ∀ j ∈ J, ∃ u ∈ F, A j ⬝ᵥ u < b j := by
                    intro j hj
                    obtain ⟨u,hu,hne⟩ := h j hj
                    exact ⟨u,hu,lt_of_le_of_ne (hle u (hsub hu) j) hne⟩
                  obtain ⟨f,hf,hflt⟩ := strictPoint q A b F hF.1 hmidF (fun u hu => hle u (hsub hu)) J hstrictF
                  obtain ⟨u,hu,huF⟩ : ∃ u ∈ S, u ∉ F := by
                    by_contra h; push Not at h; exact hFS (Set.Subset.antisymm hsub h)
                  have hfw : w ⬝ᵥ f = t := (hFeq ▸ hf).2
                  have huw : w ⬝ᵥ u < t := lt_of_le_of_ne (hwle hu) (by
                    intro he; apply huF; rw [hFeq]; exact ⟨hu,he⟩)
                  obtain ⟨c,hc,hcJ⟩ := smallStep q A b J f (f-u) (fun i hi => Or.inl (hflt i hi))
                  have hnew : f + c • (f-u) ∈ S := by
                    apply (hrep _).mpr; refine ⟨?_,hcJ⟩
                    intro i hi
                    have h1 := (hE i).mp hi f (hsub hf)
                    have h2 := (hE i).mp hi u hu
                    simp [dotProduct_add, dotProduct_smul, dotProduct_sub, h1,h2]
                  have hh : w ⬝ᵥ (f + c • (f-u)) ≤ t := hwle hnew
                  simp only [dotProduct_add,dotProduct_smul,dotProduct_sub,smul_eq_mul,hfw] at hh
                  nlinarith
                obtain ⟨j,hj,hjF⟩ := hjF
                have hyex : ∃ y, (∀ i ∈ E, A i ⬝ᵥ y = b i) ∧
                    (∀ i ∈ J.erase j, A i ⬝ᵥ y ≤ b i) ∧ b j < A j ⬝ᵥ y := by
                  by_contra h
                  have herase : P (J.erase j) := by
                    refine ⟨fun i hi => hJnot i (Finset.mem_of_mem_erase hi), ?_⟩
                    intro y; constructor
                    · intro hy; exact ⟨fun i hi => (hE i).mp hi y hy, fun i _ => hle y hy i⟩
                    · rintro ⟨he,hy⟩; apply (hrep y).mpr; refine ⟨he,?_⟩
                      intro i hi
                      by_cases hij : i = j
                      · subst i; by_contra hh
                        exact h ⟨y,he,hy,lt_of_not_ge hh⟩
                      · exact hy i (Finset.mem_erase.mpr ⟨hij,hi⟩)
                  have hcard := hJmin herase (Finset.card_erase_le)
                  have := Finset.card_erase_lt_of_mem hj
                  omega
                obtain ⟨y,hyE,hyJ,hyj⟩ := hyex
                let a : ℝ := (b j - A j ⬝ᵥ x) / (A j ⬝ᵥ y - A j ⬝ᵥ x)
                have hden : 0 < A j ⬝ᵥ y - A j ⬝ᵥ x := by have := hxlt j hj; linarith
                have ha0 : 0 < a := div_pos (sub_pos.mpr (hxlt j hj)) hden
                have ha1 : a < 1 := by dsimp [a]; rw [div_lt_one hden]; linarith
                have haeq : a * (A j ⬝ᵥ y - A j ⬝ᵥ x) = b j - A j ⬝ᵥ x := by
                  dsimp [a]; exact div_mul_cancel₀ _ hden.ne'
                let z : Fin d → ℝ := (1-a) • x + a • y
                have hzj : A j ⬝ᵥ z = b j := by
                  dsimp [z]; simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]; nlinarith
                have hzE : ∀ i ∈ E, A i ⬝ᵥ z = b i := by
                  intro i hi; have hxi := (hE i).mp hi x hx; have hyi := hyE i hi
                  dsimp [z]; simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]; nlinarith
                have hzlt : ∀ i ∈ J, i ≠ j → A i ⬝ᵥ z < b i := by
                  intro i hi hij; have hxi := hxlt i hi; have hyi := hyJ i (Finset.mem_erase.mpr ⟨hij,hi⟩)
                  dsimp [z]; simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]; nlinarith
                have hzS : z ∈ S := by
                  apply (hrep z).mpr; refine ⟨hzE,?_⟩
                  intro i hi; by_cases hij : i=j
                  · simpa [hij] using hzj.le
                  · exact (hzlt i hi hij).le
                let G := S ∩ {u | A j ⬝ᵥ u = b j}
                have hzG : z ∈ G := ⟨hzS,hzj⟩
                have hAj0 : A j ≠ 0 := by
                  intro h; have h1 := hxlt j hj
                  rw [h,zero_dotProduct] at h1
                  rw [h,zero_dotProduct] at hzj
                  linarith
                have hGface : IsFaceOf S G :=
                  ⟨⟨z,hzG⟩, Or.inr (Or.inr ⟨A j,b j,⟨hAj0,fun u hu => hle u hu j,⟨z,hzS,hzj⟩⟩,rfl⟩)⟩
                have hxnot : x ∉ G := by
                  intro h; have := hxlt j hj; have h2 : A j ⬝ᵥ x = b j := h.2; linarith
                have hdimlt : polyDim G < polyDim S := by
                  unfold polyDim; apply Submodule.finrank_lt_finrank_of_lt
                  refine lt_of_le_of_ne (vectorSpan_mono ℝ Set.inter_subset_left) ?_
                  intro heq
                  have hv := vsub_mem_vectorSpan ℝ hx hzS
                  rw [←heq] at hv
                  have hh := vs_ker G (A j) (b j) Set.inter_subset_right _ hv
                  have hh' : A j ⬝ᵥ (x-z) = 0 := hh
                  rw [dotProduct_sub,hzj] at hh'
                  have := hxlt j hj; linarith
                have hspan : vectorSpan ℝ S ≤ vectorSpan ℝ G ⊔ Submodule.span ℝ {x-z} := by
                  rw [vectorSpan_eq_span_vsub_set_right ℝ hzS, Submodule.span_le]
                  rintro v ⟨u,hu,rfl⟩
                  let c := (A j ⬝ᵥ u - b j) / (A j ⬝ᵥ x - b j)
                  let v := (u-z) - c • (x-z)
                  have hvj : A j ⬝ᵥ v = 0 := by
                    dsimp [v,c]; simp only [dotProduct_sub,dotProduct_smul,smul_eq_mul,hzj]
                    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt (hxlt j hj)))]; ring
                  have hvE : ∀ i ∈ E, A i ⬝ᵥ v = 0 := by
                    intro i hi
                    have hui := (hE i).mp hi u hu
                    have hxi := (hE i).mp hi x hx
                    dsimp [v]; simp [dotProduct_sub,dotProduct_smul,hui,hxi,hzE i hi]
                  obtain ⟨e,he,heJ⟩ := smallStep q A b J z v (by
                    intro i hi; by_cases hij : i=j
                    · subst i; exact Or.inr ⟨hvj,hzj.le⟩
                    · exact Or.inl (hzlt i hi hij))
                  have hnewG : z + e • v ∈ G := by
                    refine ⟨(hrep _).mpr ⟨?_,heJ⟩,?_⟩
                    · intro i hi; simp [dotProduct_add,dotProduct_smul,hvE i hi,hzE i hi]
                    · simp [dotProduct_add,dotProduct_smul,hvj,hzj]
                  have hvG : v ∈ vectorSpan ℝ G := by
                    have hh := vsub_mem_vectorSpan ℝ hnewG hzG
                    have hh' : e • v ∈ vectorSpan ℝ G := by simpa using hh
                    have := (vectorSpan ℝ G).smul_mem e⁻¹ hh'
                    simpa [smul_smul,inv_mul_cancel₀ he.ne'] using this
                  have h1 : v ∈ vectorSpan ℝ G ⊔ Submodule.span ℝ {x-z} := Submodule.mem_sup_left hvG
                  have h2 : c • (x-z) ∈ vectorSpan ℝ G ⊔ Submodule.span ℝ {x-z} :=
                    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
                  have hh := (vectorSpan ℝ G ⊔ Submodule.span ℝ {x-z}).add_mem h1 h2
                  simpa [v] using hh
                have hdimle : polyDim S ≤ polyDim G + 1 := by
                  have h1 := Submodule.finrank_mono hspan
                  have h2 := Submodule.finrank_add_le_finrank_add_finrank (vectorSpan ℝ G) (Submodule.span ℝ {x-z})
                  have h3 : Module.finrank ℝ (Submodule.span ℝ {x-z}) ≤ 1 := by
                    simpa using (finrank_span_le_card ({x-z} : Set (Fin d → ℝ)))
                  unfold polyDim; omega
                refine ⟨G,⟨hGface,by omega⟩,?_⟩
                intro u hu; exact ⟨hsub hu,hjF u hu⟩
              have faceSubAny : ∀ S F : Set (Fin d → ℝ), IsFaceOf S F → F ⊆ S := by
                intro S F hF
                rcases hF.2 with h | h | ⟨w,t,_,rfl⟩
                · rw [h]; exact Set.empty_subset _
                · rw [h]
                · exact Set.inter_subset_left
              have faceRestrict : ∀ S F G : Set (Fin d → ℝ), IsFaceOf S F → F ⊆ G → G ⊆ S → IsFaceOf G F := by
                intro S F G hF hFG hGS
                refine ⟨hF.1,?_⟩
                rcases hF.2 with h | h | ⟨w,t,⟨hw,hle,hne⟩,heq⟩
                · exact Or.inl h
                · right; left; exact Set.Subset.antisymm hFG (h ▸ hGS)
                · right; right
                  refine ⟨w,t,⟨hw,fun x hx => hle (hGS hx),?_⟩,?_⟩
                  · obtain ⟨x,hx⟩ := hF.1
                    exact ⟨x,hFG hx,(heq ▸ hx).2⟩
                  · apply Set.Subset.antisymm
                    · intro x hx; exact ⟨hFG hx,(heq ▸ hx).2⟩
                    · intro x hx; rw [heq]; exact ⟨hGS hx.1,hx.2⟩
              have polyInter : ∀ S F : Set (Fin d → ℝ),
                  CombOpt.MatchingPolytope.IsPolyhedron S → IsFaceOf S F →
                  CombOpt.MatchingPolytope.IsPolyhedron F := by
                intro S F hS hF
                rcases hF.2 with h | h | ⟨w,t,_,heq⟩
                · exact False.elim (by simpa [h] using hF.1)
                · rwa [h]
                · obtain ⟨q,A,b,hrep⟩ := hS
                  refine ⟨q+2, Fin.cases w (Fin.cases (-w) A), Fin.cases t (Fin.cases (-t) b), ?_⟩
                  rw [heq,hrep]
                  ext x
                  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Fin.forall_fin_succ,Fin.cases_zero,Fin.cases_succ,neg_dotProduct]
                  constructor
                  · rintro ⟨h,hx⟩; exact ⟨hx.le,by linarith,h⟩
                  · rintro ⟨h1,h2,h⟩; exact ⟨h,by linarith⟩
              have farBound : ∀ S : Set (Fin d → ℝ), CombOpt.MatchingPolytope.IsPolyhedron S →
                  ∀ F, IsFaceOf S F → ∀ i, F ∩ hyperplane M i = ∅ → ∀ z ∈ F,
                  polyRadius M p S ≤ ptDist p z (hyperplane M i) := by
                intro S
                induction hd : polyDim S using Nat.strong_induction_on generalizing S with
                | _ k IH =>
                  intro hSp F hF i hFi z hz
                  by_cases heq : F = S
                  · have hdis : hyperplane M i ∩ S = ∅ := by rw [←heq,Set.inter_comm]; exact hFi
                    have hrad : polyRadius M p S ≤ rho1 M p S := by
                      unfold polyRadius
                      cases polyDim S with
                      | zero => exact le_rfl
                      | succ k => exact min_le_left _ _
                    apply hrad.trans
                    unfold rho1
                    refine (iInf₂_le (f := fun j (_ : j ∈ {j : Fin mt | hyperplane M j ∩ S = ∅}) =>
                      setDist p S (hyperplane M j)) i hdis).trans ?_
                    unfold setDist ptDist
                    exact iInf₂_le (f := fun u (_ : u ∈ S) => ⨅ v ∈ hyperplane M i,
                      ((‖WithLp.toLp p (u-v)‖ : ℝ) : EReal)) z (heq ▸ hz)
                  · obtain ⟨G,hG,hFG⟩ := facetExtension S F hSp hF heq
                    have hGS := faceSubAny S G hG.1
                    have hsmall : polyDim G < k := by have := hG.2; omega
                    have hrec := IH _ hsmall G rfl (polyInter S G hSp hG.1) F
                      (faceRestrict S F G hF hFG hGS) i hFi z hz
                    apply le_trans ?_ hrec
                    unfold polyRadius
                    have hdim : polyDim S = polyDim G + 1 := hG.2.symm
                    rw [hdim, radiusAux]
                    apply (min_le_right _ _).trans
                    exact iInf₂_le (f := fun G' (_ : G' ∈ {G | IsFacetOf S G}) => radiusAux M p (polyDim G) G') G hG
              have farH : ∀ F, IsFaceOf T F → ∀ i, F ∩ hyperplane M i = ∅ → ∀ z ∈ F,
                  δ ≤ (M.G *ᵥ z) i - M.g0 i := by
                intro F hF i hFi z hz
                have hzT := faceSub F hF hz
                have hs0 : 0 ≤ (M.G *ᵥ z) i - M.g0 i := sub_nonneg.mpr (hTXi hzT i)
                have hle : min (εbar : EReal) (polyRadius M p T) ≤
                    (((M.G *ᵥ z) i - M.g0 i : ℝ) : EReal) :=
                  (min_le_right _ _).trans ((farBound T hTpoly F hF i hFi z hz).trans (distH i z hs0))
                rw [hδ]
                have hh := EReal.toReal_le_toReal hle (ne_bot_of_le_ne_bot (by simp) hmin0) (EReal.coe_ne_top _)
                rwa [EReal.toReal_coe] at hh
              obtain ⟨θr, hθr⟩ : ∃ θr : ℝ, θr = (thetaPoly M p T).toReal := ⟨_, rfl⟩
              have hθ01 : θr = 0 ∨ 1 ≤ θr := by
                rw [hθr]
                by_cases h : thetaPoly M p T = ⊤
                · left; rw [h]; rfl
                · right
                  have h1 : (1 : EReal) ≤ thetaPoly M p T := le_max_left _ _
                  have := EReal.toReal_le_toReal h1 (EReal.add_top_iff_ne_bot.mp rfl) h
                  simpa using this
              obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, R = fun k => alphaClaim M p T lam k * epsThm3 M p T εbar lam :=
                ⟨_, rfl⟩
              obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * θr / lam := ⟨_, rfl⟩
              have hRform : ∀ k, R k = a ^ (polyDim T - k) * (a⁻¹ ^ (polyDim T - minFaceDim T) * lam * δ) := by
                intro k; rw [hR]; simp only [alphaClaim, epsThm3, ← hθr, ← hδ, ← ha]; rw [ha, inv_div]
              have ha01 : (a = 0) ∨ 1 ≤ a := by
                rcases hθ01 with h | h
                · left; rw [ha, h]; simp
                · right; rw [ha, le_div_iff₀ hl0]; linarith
              have Rle : ∀ k, minFaceDim T ≤ k → k ≤ polyDim T → R k ≤ lam * δ := by
                intro k hk1 hk2
                rw [hRform]
                have e : a⁻¹ ^ (polyDim T - minFaceDim T) = a⁻¹ ^ (polyDim T - k) * a⁻¹ ^ (k - minFaceDim T) := by
                  rw [← pow_add]; congr 1; omega
                rw [e]
                have hX : a ^ (polyDim T - k) * (a⁻¹ ^ (polyDim T - k) * a⁻¹ ^ (k - minFaceDim T) * lam * δ)
                    = ((a * a⁻¹) ^ (polyDim T - k) * a⁻¹ ^ (k - minFaceDim T)) * (lam * δ) := by
                  rw [mul_pow]; ring
                rw [hX]
                have hld : 0 ≤ lam * δ := mul_nonneg hl0.le hδ0
                apply mul_le_of_le_one_left hld
                have hb1 : 0 ≤ a * a⁻¹ ∧ a * a⁻¹ ≤ 1 := by
                  rcases ha01 with h | h
                  · rw [h]; simp
                  · rw [mul_inv_cancel₀ (by linarith)]; simp
                have hb2 : 0 ≤ a⁻¹ ∧ a⁻¹ ≤ 1 := by
                  rcases ha01 with h | h
                  · rw [h]; simp
                  · exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ h⟩
                exact mul_le_one₀ (pow_le_one₀ hb1.1 hb1.2) (pow_nonneg hb2.1 _) (pow_le_one₀ hb2.1 hb2.2)
              have Rstep : ∀ j k, minFaceDim T ≤ j → j < k → k ≤ polyDim T → 0 < R k →
                  1 ≤ θr ∧ 2 * θr / lam * R k ≤ R j := by
                intro j k hj hjk hk hRk
                have hθ1 : 1 ≤ θr := by
                  rcases hθ01 with h | h
                  · exfalso
                    have ha0 : a = 0 := by rw [ha, h]; simp
                    rw [hRform, ha0] at hRk
                    have : (polyDim T - minFaceDim T) ≠ 0 := by omega
                    simp [zero_pow this] at hRk
                  · exact h
                refine ⟨hθ1, ?_⟩
                have ha1 : 1 ≤ a := by rw [ha, le_div_iff₀ hl0]; linarith
                rw [← ha, hRform, hRform]
                have e : a ^ (polyDim T - j) = a ^ (polyDim T - k) * a ^ (k - j) := by
                  rw [← pow_add]; congr 1; omega
                rw [e]
                have hpos : 0 < a ^ (polyDim T - k) * (a⁻¹ ^ (polyDim T - minFaceDim T) * lam * δ) := by
                  rw [hRform] at hRk; exact hRk
                have hself : a ≤ a ^ (k - j) := le_self_pow₀ ha1 (by omega)
                nlinarith
              have thetaB : 1 ≤ θr → ∀ F, IsFaceOf T F → ∀ i, (F ∩ hyperplane M i).Nonempty →
                  ∃ t : ℝ, 0 ≤ t ∧ t < 2 * θr - lam ∧ ∀ ζ ∈ F,
                    ptDist p ζ (F ∩ hyperplane M i) ≤ (t : EReal) * ptDist p ζ (hyperplane M i) := by
                intro hθ1 F hF i hne
                have hnt : thetaPoly M p T ≠ ⊤ := by
                  intro h; rw [h] at hθr; simp at hθr; linarith
                have hnb : thetaPoly M p T ≠ ⊥ :=
                  ne_bot_of_le_ne_bot (EReal.add_top_iff_ne_bot.mp rfl) (le_max_left (1 : EReal) _)
                have heq : thetaPoly M p T = (θr : EReal) := by rw [hθr, EReal.coe_toReal hnt hnb]
                have hle : thetaFace M p F i ≤ thetaPoly M p T := by
                  unfold thetaPoly
                  apply le_max_of_le_right
                  exact le_iSup₂_of_le (f := fun F (_ : F ∈ {F | IsFaceOf T F}) =>
                    ⨆ i ∈ {i : Fin mt | (F ∩ hyperplane M i).Nonempty}, thetaFace M p F i) F hF
                    (le_iSup₂_of_le (f := fun i (_ : i ∈ {i : Fin mt | (F ∩ hyperplane M i).Nonempty}) =>
                      thetaFace M p F i) i hne le_rfl)
                have hlt : thetaFace M p F i < ((2 * θr - lam : ℝ) : EReal) := by
                  rw [heq] at hle
                  exact lt_of_le_of_lt hle (EReal.coe_lt_coe_iff.mpr (by linarith))
                unfold thetaFace at hlt
                rw [sInf_lt_iff] at hlt
                obtain ⟨_, ⟨t, ht0, rfl, hprop⟩, htl⟩ := hlt
                exact ⟨t, ht0, EReal.coe_lt_coe_iff.mp htl, hprop⟩
              have main : ∀ k, minFaceDim T ≤ k → k ≤ polyDim T → ∀ F, IsFaceOf T F → polyDim F = k →
                  ∀ zhat ∈ F, ∃ zbar ∈ F, ‖WithLp.toLp p (zbar - zhat)‖ + R k ≤ lam * δ ∧
                    ∀ i, (M.G *ᵥ zbar) i = M.g0 i ∨
                      ‖WithLp.toLp p (zbar - zhat)‖ + R k ≤ lam * ((M.G *ᵥ zbar) i - M.g0 i) := by
                intro k
                induction k using Nat.strong_induction_on with
                | _ k IH =>
                intro hk1 hk2 F hF hdim zhat hzhat
                have hzX : zhat ∈ Xi M := hTXi (faceSub F hF hzhat)
                by_cases hB : ∃ i, (F ∩ hyperplane M i).Nonempty ∧ zhat ∉ hyperplane M i ∧
                    lam * ((M.G *ᵥ zhat) i - M.g0 i) < R k
                · obtain ⟨i, hne, hzi, hlt⟩ := hB
                  have hs0 : 0 ≤ (M.G *ᵥ zhat) i - M.g0 i := sub_nonneg.mpr (hzX i)
                  have hRk : 0 < R k := lt_of_le_of_lt (mul_nonneg hl0.le hs0) hlt
                  have hnsub : ¬ F ⊆ hyperplane M i := fun h => hzi (h hzhat)
                  have hFi := faceInter F hF i hne
                  have hjk := dimdrop F i hne hnsub
                  rw [hdim] at hjk
                  have hj1 : minFaceDim T ≤ polyDim (F ∩ hyperplane M i) := hmin _ hFi
                  obtain ⟨hθ1, hstep⟩ := Rstep _ k hj1 hjk hk2 hRk
                  obtain ⟨t, ht0, htlt, htprop⟩ := thetaB hθ1 F hF i hne
                  have hd := htprop zhat hzhat
                  have hdH := distH i zhat hs0
                  have hb : ptDist p zhat (F ∩ hyperplane M i) <
                      (((2 * θr - lam) * R k / lam : ℝ) : EReal) := by
                    have h0 : 0 ≤ ptDist p zhat (hyperplane M i) := by
                      unfold ptDist; exact le_iInf₂ (fun _ _ => EReal.coe_nonneg.mpr (norm_nonneg _))
                    have hnt : ptDist p zhat (hyperplane M i) ≠ ⊤ :=
                      ne_top_of_le_ne_top (EReal.coe_ne_top _) hdH
                    have hnb : ptDist p zhat (hyperplane M i) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
                    rw [← EReal.coe_toReal hnt hnb] at hdH hd
                    rw [← EReal.coe_mul] at hd
                    refine lt_of_le_of_lt hd (EReal.coe_lt_coe_iff.mpr ?_)
                    rw [EReal.coe_le_coe_iff] at hdH
                    have hs : (M.G *ᵥ zhat) i - M.g0 i < R k / lam := by rw [lt_div_iff₀ hl0]; linarith
                    calc t * (ptDist p zhat (hyperplane M i)).toReal ≤ t * (R k / lam) :=
                          mul_le_mul_of_nonneg_left (hdH.trans hs.le) ht0
                      _ < (2 * θr - lam) * (R k / lam) := mul_lt_mul_of_pos_right htlt (div_pos hRk hl0)
                      _ = _ := by ring
                  unfold ptDist at hb
                  rw [iInf_lt_iff] at hb; obtain ⟨z1, hb⟩ := hb
                  rw [iInf_lt_iff] at hb; obtain ⟨hz1, hb⟩ := hb
                  rw [EReal.coe_lt_coe_iff] at hb
                  obtain ⟨zbar, hzbar, h1, h2⟩ := IH _ hjk hj1 (by omega) _ hFi rfl z1 hz1
                  have htri : ‖WithLp.toLp p (zbar - zhat)‖ ≤
                      ‖WithLp.toLp p (zbar - z1)‖ + ‖WithLp.toLp p (zhat - z1)‖ := by
                    have : zbar - zhat = (zbar - z1) - (zhat - z1) := by abel
                    rw [this, WithLp.toLp_sub]; exact norm_sub_le _ _
                  have hkey : ‖WithLp.toLp p (zbar - zhat)‖ + R k ≤
                      ‖WithLp.toLp p (zbar - z1)‖ + R (polyDim (F ∩ hyperplane M i)) := by
                    have : (2 * θr - lam) * R k / lam + R k = 2 * θr / lam * R k := by
                      field_simp; ring
                    linarith
                  refine ⟨zbar, hzbar.1, by linarith, fun i' => ?_⟩
                  rcases h2 i' with h | h
                  · exact Or.inl h
                  · exact Or.inr (by linarith)
                · push Not at hB
                  refine ⟨zhat, hzhat, ?_, fun i => ?_⟩
                  · simp only [sub_self, WithLp.toLp_zero, norm_zero, zero_add]; exact Rle k hk1 hk2
                  · by_cases hzi : zhat ∈ hyperplane M i
                    · exact Or.inl hzi
                    · right; simp only [sub_self, WithLp.toLp_zero, norm_zero, zero_add]
                      by_cases hne : (F ∩ hyperplane M i).Nonempty
                      · exact hB i hne hzi
                      · have h1 := farH F hF i (Set.not_nonempty_iff_eq_empty.mp hne) zhat hzhat
                        have h2 := Rle k hk1 hk2
                        nlinarith
              intro k hk1 hk2 F hF hdim zhat hzhat
              obtain ⟨zbar, hzbar, h1, h2⟩ := main k hk1 hk2 F hF hdim zhat hzhat
              have hRk : alphaClaim M p T lam k * epsThm3 M p T εbar lam = R k := by rw [hR]
              rw [hRk]
              refine ⟨zbar, hzbar, ?_⟩
              apply reduce zhat (R k) zbar (hTXi (faceSub F hF hzbar))
              intro ζ hζ
              have hb : ‖WithLp.toLp p (ζ - zhat)‖ ≤ R k := hζ.1
              have htri : ‖WithLp.toLp p (ζ - zbar)‖ ≤
                  ‖WithLp.toLp p (ζ - zhat)‖ + ‖WithLp.toLp p (zbar - zhat)‖ := by
                have : ζ - zbar = (ζ - zhat) - (zbar - zhat) := by abel
                rw [this, WithLp.toLp_sub]; exact norm_sub_le _ _
              have hle : lam * δ ≤ lam * εbar := mul_le_mul_of_nonneg_left hδε hl0.le
              refine ⟨by linarith, fun i => ?_⟩
              rcases h2 i with h | h
              · exact Or.inl h
              · exact Or.inr (by linarith)
