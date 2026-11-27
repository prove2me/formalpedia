-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:27.741955+00:00
-- url     : https://prove2.me/submissions/25305a50-7f0f-40ee-a81f-f09b17936534

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

open TwoStageSRO
open TwoStageSRO.AsymOpt
open TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 48, Theorem 3:
let `T ⊆ Ξ` be a nonempty polyhedron. Given `ϵ̄ > 0` and `λ ∈ (0, 1)`, define
`ϵ = (λ / (2θ^T_Ξ))^{dim(T) − dim̲(T)} λ min{ϵ̄, ∆_Ξ(T)}`. Then for all `ζ̂ ∈ T` there is `ζ̄ ∈ T` with
`B(ζ̂, ϵ) ∩ Ξ ⊆ {λζ + (1 − λ)ζ̄ : ζ ∈ B(ζ̄, ϵ̄) ∩ Ξ}`.

**Formalization Note** `ϵ` is `epsThm3 M p T εbar lam`, built from `θ^T_Ξ` (`thetaPoly`, Definition 4),
`∆_Ξ(T)` (`polyRadius`, Definition 3), `dim` and `dim̲`. The standing normalization `‖gᵢ‖_* = 1`
(p. 33) is `hG`; minimality of the representation of `Ξ` is not imposed (a disclosed strengthening). -/
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty)
    (εbar : ℝ) (hεbar : 0 < εbar) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ zhat ∈ T, ∃ zbar ∈ T,
      ball p zhat (epsThm3 M p T εbar lam) ∩ Xi M ⊆
        (fun ζ => lam • ζ + (1 - lam) • zbar) '' (ball p zbar εbar ∩ Xi M) := by
          classical
          obtain ⟨hl0, hl1⟩ := hlam
          set ε := epsThm3 M p T εbar lam with hεdef
          have hConstSpan : ∀ (P : Set (Fin d → ℝ)) (w : Fin d → ℝ) (t : ℝ),
              (∀ x ∈ P, w ⬝ᵥ x = t) → ∀ v ∈ vectorSpan ℝ P, w ⬝ᵥ v = 0 := by
            intro P w t h
            have hs : vectorSpan ℝ P ≤ LinearMap.ker (dotProductBilin ℝ ℝ w) := by
              apply Submodule.span_le.mpr
              rintro _ ⟨x, hx, y, hy, rfl⟩
              change w ⬝ᵥ (x - y) = 0
              rw [dotProduct_sub, h x hx, h y hy, sub_self]
            exact fun v hv => hs hv
          have hFaceSub : ∀ {P F : Set (Fin d → ℝ)}, IsFaceOf P F → F ⊆ P := by
            rintro P F ⟨hne, h | h | ⟨w, t, hw, he⟩⟩
            · exact hne.ne_empty h |>.elim
            · exact h ▸ Set.Subset.rfl
            · rw [he]; exact Set.inter_subset_left
          have hDimCut : ∀ {P F : Set (Fin d → ℝ)} (w : Fin d → ℝ) (t : ℝ),
              F.Nonempty → F ⊆ P → (∀ x ∈ F, w ⬝ᵥ x = t) →
              (∃ x ∈ P, w ⬝ᵥ x ≠ t) → polyDim F < polyDim P := by
            intro P F w t hne hsub heq hne'
            have hle := vectorSpan_mono ℝ hsub
            apply Submodule.finrank_lt_finrank_of_lt
            apply lt_of_le_of_ne hle
            intro he
            obtain ⟨y, hy⟩ := hne
            obtain ⟨x, hx, hxy⟩ := hne'
            have hv : x - y ∈ vectorSpan ℝ F := by
              rw [he]; exact vsub_mem_vectorSpan ℝ hx (hsub hy)
            have hz := hConstSpan F w t heq (x - y) hv
            rw [dotProduct_sub, heq y hy] at hz
            exact hxy (by linarith)
          have hFaceDim : ∀ {P F : Set (Fin d → ℝ)}, IsFaceOf P F →
              F ≠ P → polyDim F < polyDim P := by
            intro P F hF hne
            rcases hF.2 with he | he | ⟨w, t, hw, he⟩
            · exact (hF.1.ne_empty he).elim
            · exact (hne he).elim
            · apply hDimCut w t hF.1 (hFaceSub hF)
              · intro x hx; rw [he] at hx; exact hx.2
              · by_contra! h
                apply hne
                rw [he]
                exact Set.inter_eq_left.mpr h
          have hFacePoly : ∀ {P F : Set (Fin d → ℝ)},
              CombOpt.MatchingPolytope.IsPolyhedron P → IsFaceOf P F →
              CombOpt.MatchingPolytope.IsPolyhedron F := by
            intro P F hP hF
            rcases hF.2 with he | he | ⟨w, t, hw, he⟩
            · exact (hF.1.ne_empty he).elim
            · simpa [he] using hP
            · obtain ⟨a, A, b, hP⟩ := hP
              refine ⟨a + 2, (fun i => if h : i.val < a then A ⟨i.val, h⟩
                else if i.val = a then w else -w),
                (fun i => if h : i.val < a then b ⟨i.val, h⟩
                else if i.val = a then t else -t), ?_⟩
              rw [he, hP]
              ext x
              constructor
              · rintro ⟨hx, heq⟩ i
                dsimp
                split_ifs with hi hi
                · exact hx _
                · exact heq.le
                · simpa [neg_dotProduct] using neg_le_neg heq.ge
              · intro hx
                constructor
                · intro i
                  simpa only [dif_pos i.isLt] using hx ⟨i.val, by omega⟩
                · have h1 := hx ⟨a, by omega⟩
                  have h2 := hx ⟨a + 1, by omega⟩
                  simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte] at h1
                  simp only [show ¬ a + 1 < a by omega, ↓reduceDIte,
                    show a + 1 ≠ a by omega, ↓reduceIte, neg_dotProduct] at h2
                  exact le_antisymm h1 (by linarith)
          have hConstAff : ∀ (P : Set (Fin d → ℝ)) (w : Fin d → ℝ) (t : ℝ),
              (∀ x ∈ P, w ⬝ᵥ x = t) → ∀ x ∈ affineSpan ℝ P, w ⬝ᵥ x = t := by
            intro P w t hh x hx
            rcases hx with ⟨y, hy, v, hv, rfl⟩
            change w ⬝ᵥ (v + y) = t
            rw [dotProduct_add, hConstSpan P w t hh v hv, hh y hy, zero_add]
          have hConv : ∀ {P : Set (Fin d → ℝ)},
              CombOpt.MatchingPolytope.IsPolyhedron P → Convex ℝ P := by
            rintro P ⟨a, A, b, rfl⟩
            intro x hx y hy u v hu hv huv i
            simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
            calc
              _ ≤ u * b i + v * b i := add_le_add
                (mul_le_mul_of_nonneg_left (hx i) hu) (mul_le_mul_of_nonneg_left (hy i) hv)
              _ = b i := by rw [← add_mul, huv, one_mul]
          have hStrictPoint : ∀ {a : ℕ} (P : Set (Fin d → ℝ))
              (A : Fin a → Fin d → ℝ) (b : Fin a → ℝ) (s : Finset (Fin a)),
              P.Nonempty → Convex ℝ P → (∀ x ∈ P, ∀ i ∈ s, A i ⬝ᵥ x ≤ b i) →
              (∀ i ∈ s, ∃ x ∈ P, A i ⬝ᵥ x < b i) →
              ∃ x ∈ P, ∀ i ∈ s, A i ⬝ᵥ x < b i := by
            intro a P A b s hne hcv hle hex
            induction s using Finset.induction_on with
            | empty =>
              obtain ⟨x, hx⟩ := hne
              exact ⟨x, hx, by simp⟩
            | @insert i s hi ih =>
              obtain ⟨x, hx, hxs⟩ := ih (fun x hx j hj => hle x hx j (Finset.mem_insert_of_mem hj))
                (fun j hj => hex j (Finset.mem_insert_of_mem hj))
              obtain ⟨y, hy, hyi⟩ := hex i (Finset.mem_insert_self _ _)
              refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y,
                hcv hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
              intro j hj
              simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
              rcases Finset.mem_insert.mp hj with rfl | hj
              · have := hle x hx j (Finset.mem_insert_self _ _); linarith
              · have := hle y hy j (Finset.mem_insert_of_mem hj)
                have := hxs j hj; linarith
          have hSmall : ∀ {a : ℕ} (A : Fin a → Fin d → ℝ) (b : Fin a → ℝ)
              (s : Finset (Fin a)) (z v : Fin d → ℝ),
              (∀ i ∈ s, A i ⬝ᵥ z < b i) →
              ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, A i ⬝ᵥ (z + t • v) < b i := by
            intro a A b s z v hz
            have hh : ∀ᶠ t : ℝ in nhds 0, ∀ i ∈ s, A i ⬝ᵥ (z + t • v) < b i := by
              apply (Finset.eventually_all s).mpr
              intro i hi
              have hc : Continuous (fun t : ℝ => A i ⬝ᵥ (z + t • v)) := by
                unfold dotProduct
                fun_prop
              exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa using hz i hi))
            have hh' : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
                ∀ i ∈ s, A i ⬝ᵥ (z + t • v) < b i := hh.filter_mono nhdsWithin_le_nhds
            have ht : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
            exact (ht.and hh').exists
          have hFacetExtend : ∀ {P F : Set (Fin d → ℝ)},
              CombOpt.MatchingPolytope.IsPolyhedron P → IsFaceOf P F → F ≠ P →
              ∃ H, IsFacetOf P H ∧ F ⊆ H := by
            intro P F hP hF hFP
            obtain ⟨a, A, b, hArep⟩ := hP
            let R : Finset (Fin a) → Prop := fun s =>
              ∀ x ∈ affineSpan ℝ P, (∀ i ∈ s, A i ⬝ᵥ x ≤ b i) → x ∈ P
            have hRuniv : R Finset.univ := by
              intro x hx hi
              rw [hArep]
              exact fun i => hi i (Finset.mem_univ _)
            obtain ⟨s, hs, hmin⟩ := exists_minimalFor_of_wellFoundedLT R Finset.card ⟨_, hRuniv⟩
            have hle : ∀ x ∈ P, ∀ i : Fin a, A i ⬝ᵥ x ≤ b i := by
              intro x hx; simpa only [hArep, Set.mem_ofPred_eq] using hx
            have hir : ∀ i ∈ s, ∃ y ∈ affineSpan ℝ P,
                (∀ j ∈ s.erase i, A j ⬝ᵥ y ≤ b j) ∧ b i < A i ⬝ᵥ y := by
              intro i hi
              have hn : ¬ R (s.erase i) := by
                intro hh
                have := hmin hh Finset.card_erase_le
                have := Finset.card_erase_lt_of_mem hi
                omega
              simp only [R, not_forall, exists_prop] at hn
              obtain ⟨y, hy, hys, hyP⟩ := hn
              refine ⟨y, hy, hys, ?_⟩
              by_contra! hb
              apply hyP
              apply hs y hy
              intro j hj
              by_cases hji : j = i
              · simpa [hji] using hb
              · exact hys j (Finset.mem_erase.mpr ⟨hji, hj⟩)
            have hstrict : ∀ i ∈ s, ∃ x ∈ P, A i ⬝ᵥ x < b i := by
              intro i hi
              by_contra! hn
              have heq : ∀ x ∈ P, A i ⬝ᵥ x = b i := fun x hx => le_antisymm (hle x hx i) (hn x hx)
              obtain ⟨y, hy, hys, hyi⟩ := hir i hi
              have := hConstAff P (A i) (b i) heq y hy
              linarith
            obtain ⟨x, hx, hxs⟩ := hStrictPoint P A b s
              (hF.1.mono (hFaceSub hF)) (hConv ⟨a, A, b, hArep⟩)
              (fun x hx i _ => hle x hx i) hstrict
            have hfacets : ∀ i ∈ s, IsFacetOf P (P ∩ {z | A i ⬝ᵥ z = b i}) := by
              intro i hi
              obtain ⟨y, hy, hys, hyi⟩ := hir i hi
              let t : ℝ := (b i - A i ⬝ᵥ x) / (A i ⬝ᵥ y - A i ⬝ᵥ x)
              have hxi := hxs i hi
              have hden : 0 < A i ⬝ᵥ y - A i ⬝ᵥ x := by linarith
              have ht0 : 0 < t := div_pos (by linarith) hden
              have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
              have ht : t * (A i ⬝ᵥ y - A i ⬝ᵥ x) = b i - A i ⬝ᵥ x := div_mul_cancel₀ _ hden.ne'
              let z := x + t • (y - x)
              have hzA : z ∈ affineSpan ℝ P := by
                have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
                  (subset_affineSpan ℝ P hx)
                  ((vectorSpan ℝ P).smul_mem t
                    (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hy (subset_affineSpan ℝ P hx)))
                simpa [z, vadd_eq_add, add_comm] using this
              have hzi : A i ⬝ᵥ z = b i := by
                dsimp [z]; rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]; linarith
              have hzs : ∀ j ∈ s.erase i, A j ⬝ᵥ z < b j := by
                intro j hj
                have hj' := (Finset.mem_erase.mp hj).2
                have hxj := hxs j hj'
                have hyj := hys j hj
                dsimp [z]; rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
                nlinarith
              have hzP : z ∈ P := hs z hzA (by
                intro j hj
                by_cases hji : j = i
                · simpa [hji] using hzi.le
                · exact (hzs j (Finset.mem_erase.mpr ⟨hji, hj⟩)).le)
              let H := P ∩ {z | A i ⬝ᵥ z = b i}
              have hzH : z ∈ H := ⟨hzP, hzi⟩
              have hneAi : A i ≠ 0 := by
                intro hh; simp [hh] at hxi hzi; linarith
              have hface : IsFaceOf P H := ⟨⟨z, hzH⟩, Or.inr (Or.inr ⟨A i, b i,
                ⟨hneAi, fun u hu => hle u hu i, z, hzH⟩, rfl⟩)⟩
              have hkernel : ∀ v ∈ vectorSpan ℝ P, A i ⬝ᵥ v = 0 → v ∈ vectorSpan ℝ H := by
                intro v hv hvi
                obtain ⟨c, hc, hcs⟩ := hSmall A b (s.erase i) z v hzs
                have hzvA : z + c • v ∈ affineSpan ℝ P := by
                  have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hzA
                    ((vectorSpan ℝ P).smul_mem c hv)
                  simpa [vadd_eq_add, add_comm] using this
                have hzvi : A i ⬝ᵥ (z + c • v) = b i := by
                  simp [dotProduct_add, dotProduct_smul, hvi, hzi]
                have hzvP : z + c • v ∈ P := hs _ hzvA (by
                  intro j hj
                  by_cases hji : j = i
                  · simpa [hji] using hzvi.le
                  · exact (hcs j (Finset.mem_erase.mpr ⟨hji, hj⟩)).le)
                have hv' := vsub_mem_vectorSpan ℝ (show z + c • v ∈ H from ⟨hzvP, hzvi⟩) hzH
                have hv'' := (vectorSpan ℝ H).smul_mem c⁻¹ hv'
                simpa only [vsub_eq_sub, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hv''
              let u := x - z
              have hu : u ∈ vectorSpan ℝ P := vsub_mem_vectorSpan ℝ hx hzP
              have hui : A i ⬝ᵥ u ≠ 0 := by
                dsimp [u]; rw [dotProduct_sub, hzi]; linarith
              have hspan : vectorSpan ℝ P ≤ vectorSpan ℝ H ⊔ Submodule.span ℝ {u} := by
                intro v hv
                let c := (A i ⬝ᵥ v) / (A i ⬝ᵥ u)
                have hvk : v - c • u ∈ vectorSpan ℝ H := by
                  apply hkernel _ ((vectorSpan ℝ P).sub_mem hv ((vectorSpan ℝ P).smul_mem c hu))
                  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
                  dsimp [c]; rw [div_mul_cancel₀ _ hui, sub_self]
                have hcu : c • u ∈ Submodule.span ℝ ({u} : Set (Fin d → ℝ)) :=
                  Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
                exact Submodule.mem_sup.mpr ⟨_, hvk, _, hcu, sub_add_cancel _ _⟩
              have hdimle : polyDim P ≤ polyDim H + 1 := by
                have hh := Submodule.finrank_mono hspan
                have hhSup := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ H)
                  (Submodule.span ℝ ({u} : Set (Fin d → ℝ)))
                have hh' : Module.finrank ℝ (Submodule.span ℝ ({u} : Set (Fin d → ℝ))) ≤ 1 :=
                  by
                    have hu0 : u ≠ 0 := by
                      intro hh; apply hui; rw [hh]; simp
                    exact (finrank_span_singleton hu0).le
                unfold polyDim
                omega
              have hdimlt : polyDim H < polyDim P := by
                apply hFaceDim hface
                intro he
                have : x ∈ H := he.symm ▸ hx
                have hh : A i ⬝ᵥ x = b i := this.2; linarith
              exact ⟨hface, by change polyDim H + 1 = polyDim P; omega⟩
            rcases hF.2 with he | he | ⟨w, t, hw, he⟩
            · exact (hF.1.ne_empty he).elim
            · exact (hFP he).elim
            have hproper : ∃ y ∈ P, w ⬝ᵥ y < t := by
              by_contra! hn
              apply hFP
              rw [he]
              apply Set.inter_eq_left.mpr
              intro y hy
              exact le_antisymm (hw.2.1 hy) (hn y hy)
            let sF := s.filter (fun i => ∃ y ∈ F, A i ⬝ᵥ y < b i)
            obtain ⟨z, hzF, hzsF⟩ := hStrictPoint F A b sF hF.1
              (hConv (hFacePoly ⟨a, A, b, hArep⟩ hF))
              (fun y hy i _ => hle y (hFaceSub hF hy) i)
              (fun i hi => (Finset.mem_filter.mp hi).2)
            have hactive : ∃ i ∈ s, A i ⬝ᵥ z = b i := by
              by_contra! hn
              have hzs : ∀ i ∈ s, A i ⬝ᵥ z < b i := fun i hi =>
                lt_of_le_of_ne (hle z (hFaceSub hF hzF) i) (hn i hi)
              obtain ⟨y, hy, hyw⟩ := hproper
              obtain ⟨c, hc, hcs⟩ := hSmall A b s z (z - y) hzs
              have hzA := subset_affineSpan ℝ P (hFaceSub hF hzF)
              have hnewA : z + c • (z - y) ∈ affineSpan ℝ P := by
                have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hzA
                  ((vectorSpan ℝ P).smul_mem c (vsub_mem_vectorSpan ℝ (hFaceSub hF hzF) hy))
                simpa [vadd_eq_add, add_comm] using this
              have hnewP := hs _ hnewA (fun i hi => (hcs i hi).le)
              have hzw : w ⬝ᵥ z = t := by rw [he] at hzF; exact hzF.2
              have hh : w ⬝ᵥ (z + c • (z - y)) ≤ t := hw.2.1 hnewP
              rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul, hzw] at hh
              nlinarith
            obtain ⟨i, hi, hzi⟩ := hactive
            refine ⟨P ∩ {z | A i ⬝ᵥ z = b i}, hfacets i hi, ?_⟩
            intro y hy
            refine ⟨hFaceSub hF hy, ?_⟩
            apply le_antisymm (hle y (hFaceSub hF hy) i)
            by_contra! hlt
            have := hzsF i (Finset.mem_filter.mpr ⟨hi, y, hy, hlt⟩)
            linarith
          have hMinDim : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F → minFaceDim T ≤ polyDim F := by
            intro F hF
            obtain ⟨F₀, h₀, hmin⟩ := exists_minimalFor_of_wellFoundedLT
              (fun E : Set (Fin d → ℝ) => IsFaceOf T E ∧ E ⊆ F) polyDim ⟨F, hF, Set.Subset.rfl⟩
            have hm : IsMinimalFaceOf T F₀ := by
              refine ⟨h₀.1, ?_⟩
              intro F' hF' hsub
              by_contra hn
              have hdim : polyDim F' < polyDim F₀ := by
                rcases hF'.2 with he | he | ⟨w, t, hw, he⟩
                · exact (hF'.1.ne_empty he).elim
                · have : F₀ = T := Set.Subset.antisymm (hFaceSub h₀.1) (he ▸ hsub)
                  exact (hn (he.trans this.symm)).elim
                · apply hDimCut w t hF'.1 hsub
                  · intro x hx; rw [he] at hx; exact hx.2
                  · by_contra! hh
                    apply hn
                    apply Set.Subset.antisymm hsub
                    intro x hx
                    rw [he]
                    exact ⟨hFaceSub h₀.1 hx, hh x hx⟩
              exact (not_lt_of_ge (hmin ⟨hF', hsub.trans h₀.2⟩ hdim.le)) hdim
            have h₁ : minFaceDim T ≤ polyDim F₀ := Nat.sInf_le ⟨F₀, hm, rfl⟩
            exact h₁.trans (Submodule.finrank_mono (vectorSpan_mono ℝ h₀.2))
          have hFaceMono : ∀ {P F H : Set (Fin d → ℝ)},
              IsFaceOf P F → H ⊆ P → F ⊆ H → IsFaceOf H F := by
            intro P F H hF hHP hFH
            refine ⟨hF.1, ?_⟩
            rcases hF.2 with he | he | ⟨w, t, hw, he⟩
            · exact (hF.1.ne_empty he).elim
            · exact Or.inr (Or.inl (Set.Subset.antisymm hFH (he.symm ▸ hHP)))
            · refine Or.inr (Or.inr ⟨w, t, ⟨hw.1, fun x hx => hw.2.1 (hHP hx), ?_⟩, ?_⟩)
              · obtain ⟨x, hx⟩ := hF.1
                exact ⟨x, hFH hx, (he ▸ hx).2⟩
              · apply Set.Subset.antisymm
                · intro x hx; exact ⟨hFH hx, (he ▸ hx).2⟩
                · intro x hx; rw [he]; exact ⟨hHP hx.1, hx.2⟩
          have hRadRho : ∀ P : Set (Fin d → ℝ), polyRadius M p P ≤ rho1 M p P := by
            intro P
            unfold polyRadius
            cases polyDim P with
            | zero => exact le_rfl
            | succ k => exact min_le_left _ _
          have hRadFace : ∀ {P F : Set (Fin d → ℝ)},
              CombOpt.MatchingPolytope.IsPolyhedron P → IsFaceOf P F →
              polyRadius M p P ≤ polyRadius M p F := by
            intro P
            induction hk : polyDim P using Nat.strong_induction_on generalizing P with
            | h k ih =>
              intro F hP hF
              by_cases he : F = P
              · rw [he]
              obtain ⟨H, hH, hFH⟩ := hFacetExtend hP hF he
              have hdim : polyDim H < k := by have := hH.2; omega
              have hstep : polyRadius M p P ≤ polyRadius M p H := by
                unfold polyRadius
                rw [← hH.2, radiusAux]
                exact (min_le_right _ _).trans (iInf_le_of_le H (iInf_le_of_le hH le_rfl))
              exact hstep.trans (ih (polyDim H) hdim rfl (hFacePoly hP hH.1)
                (hFaceMono hF (hFaceSub hH.1) hFH))
          have hRadNonneg : ∀ P : Set (Fin d → ℝ), 0 ≤ polyRadius M p P := by
            have hrho : ∀ P : Set (Fin d → ℝ), 0 ≤ rho1 M p P := by
              intro P
              unfold rho1 setDist
              exact le_iInf₂ (fun _ _ => le_iInf₂ (fun _ _ => le_iInf₂ (fun _ _ => by positivity)))
            have haux : ∀ k (P : Set (Fin d → ℝ)), 0 ≤ radiusAux M p k P := by
              intro k
              induction k with
              | zero => exact hrho
              | succ k ih =>
                intro P
                exact le_min (hrho P) (le_iInf₂ (fun F _ => ih F))
            exact fun P => haux _ P
          let R : ℝ := (min (εbar : EReal) (polyRadius M p T)).toReal
          have hR0 : 0 ≤ R := EReal.toReal_nonneg (le_min (by positivity) (hRadNonneg T))
          have hRcoe : (R : EReal) = min (εbar : EReal) (polyRadius M p T) := by
            apply EReal.coe_toReal
            · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_left _ _)
            · exact ne_of_gt (lt_of_lt_of_le (by exact EReal.bot_lt_coe 0)
                (le_min (by positivity) (hRadNonneg T)))
          have hRbar : R ≤ εbar := by
            exact_mod_cast (hRcoe ▸ min_le_left (εbar : EReal) (polyRadius M p T))
          have hRrad : (R : EReal) ≤ polyRadius M p T := by rw [hRcoe]; exact min_le_right _ _
          have hRadDist : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F →
              ∀ z ∈ F, ∀ i, F ∩ hyperplane M i = ∅ → (R : EReal) ≤ ptDist p z (hyperplane M i) := by
            intro F hF z hz i hi
            calc
              (R : EReal) ≤ polyRadius M p T := hRrad
              _ ≤ polyRadius M p F := hRadFace hTpoly hF
              _ ≤ rho1 M p F := hRadRho F
              _ ≤ setDist p F (hyperplane M i) := by
                exact iInf_le_of_le i (iInf_le_of_le
                  (show hyperplane M i ∩ F = ∅ by simpa [Set.inter_comm] using hi) le_rfl)
              _ ≤ ptDist p z (hyperplane M i) := iInf_le_of_le z (iInf_le_of_le hz le_rfl)
          have hHold : ∀ i (u : Fin d → ℝ), M.G i ⬝ᵥ u ≤ ‖WithLp.toLp p u‖ := by
            intro i u
            have hbdd : BddAbove ((fun u => u ⬝ᵥ M.G i) '' {u : Fin d → ℝ | ‖WithLp.toLp p u‖ ≤ 1}) := by
              by_contra hb
              have := hG i
              unfold dualNorm at this
              rw [Real.sSup_of_not_bddAbove hb] at this
              norm_num at this
            by_cases hu : ‖WithLp.toLp p u‖ = 0
            · have : u = 0 := by
                have := norm_eq_zero.mp hu
                simpa using congrArg (WithLp.ofLp) this
              subst this; simp
            · have hpos : 0 < ‖WithLp.toLp p u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
              set c := ‖WithLp.toLp p u‖
              have hmem : (c⁻¹ • u) ∈ {u : Fin d → ℝ | ‖WithLp.toLp p u‖ ≤ 1} := by
                show ‖WithLp.toLp p (c⁻¹ • u)‖ ≤ 1
                rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
                  inv_mul_cancel₀ hu]
              have h1 : (c⁻¹ • u) ⬝ᵥ M.G i ≤ 1 := by
                have := le_csSup hbdd ⟨_, hmem, rfl⟩
                rw [← hG i] ; exact this
              rw [smul_dotProduct, smul_eq_mul, dotProduct_comm] at h1
              have := mul_le_mul_of_nonneg_left h1 hpos.le
              rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, mul_one] at this
              exact this
          have hFaceFrom : ∀ (P : Set (Fin d → ℝ)) (w : Fin d → ℝ) (t : ℝ),
              (∀ x ∈ P, w ⬝ᵥ x ≤ t) → (P ∩ {x | w ⬝ᵥ x = t}).Nonempty →
              IsFaceOf P (P ∩ {x | w ⬝ᵥ x = t}) := by
            intro P w t hv hne
            refine ⟨hne, ?_⟩
            by_cases hw : w = 0
            · obtain ⟨x, hx, hxt⟩ := hne
              have ht : t = 0 := by simpa [hw] using hxt.symm
              exact Or.inr (Or.inl (by simp [hw, ht]))
            · exact Or.inr (Or.inr ⟨w, t, ⟨hw, fun x hx => hv x hx, hne⟩, rfl⟩)
          have hFaceRep : ∀ {P F : Set (Fin d → ℝ)}, IsFaceOf P F →
              ∃ (w : Fin d → ℝ) (t : ℝ), (∀ x ∈ P, w ⬝ᵥ x ≤ t) ∧ F = P ∩ {x | w ⬝ᵥ x = t} := by
            intro P F hF
            rcases hF.2 with he | he | ⟨w, t, hw, he⟩
            · exact (hF.1.ne_empty he).elim
            · exact ⟨0, 0, by simp, by simpa using he⟩
            · exact ⟨w, t, fun x hx => hw.2.1 hx, he⟩
          have hCut : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F →
              ∀ i, (F ∩ hyperplane M i).Nonempty → IsFaceOf T (F ∩ hyperplane M i) := by
            intro F hF i hne
            obtain ⟨w, t, hw, he⟩ := hFaceRep hF
            have hGi : ∀ x ∈ T, M.g0 i ≤ M.G i ⬝ᵥ x := fun x hx => hTXi hx i
            have he' : F ∩ hyperplane M i = T ∩ {x | (w - M.G i) ⬝ᵥ x = t - M.g0 i} := by
              ext x
              simp only [he, Set.mem_inter_iff, Set.mem_ofPred_eq, hyperplane]
              constructor
              · rintro ⟨⟨hx, hxt⟩, hxi⟩
                refine ⟨hx, ?_⟩
                rw [sub_dotProduct, hxt]; change t - (M.G *ᵥ x) i = _; rw [hxi]
              · rintro ⟨hx, hxe⟩
                rw [sub_dotProduct] at hxe
                have h1 := hw x hx
                have h2 := hGi x hx
                exact ⟨⟨hx, by linarith⟩, by change M.G i ⬝ᵥ x = M.g0 i; linarith⟩
            rw [he']
            apply hFaceFrom
            · intro x hx
              rw [sub_dotProduct]
              linarith [hw x hx, hGi x hx]
            · exact he' ▸ hne
          have hUnit : ∀ i, ∃ u : Fin d → ℝ, ‖WithLp.toLp p u‖ ≤ 1 ∧ M.G i ⬝ᵥ u = 1 := by
            intro i
            let f : PiLp p (fun _ : Fin d => ℝ) → ℝ := fun u => M.G i ⬝ᵥ WithLp.ofLp u
            have hf : Continuous f := by
              dsimp [f]
              unfold dotProduct
              fun_prop
            obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall (0 : PiLp p (fun _ : Fin d => ℝ)) 1).exists_isMaxOn
              (by exact ⟨0, by simp⟩) hf.continuousOn
            have hun : ‖u‖ ≤ 1 := by simpa using hu
            have hgreat : IsGreatest ((fun v => v ⬝ᵥ M.G i) ''
                {v : Fin d → ℝ | ‖WithLp.toLp p v‖ ≤ 1}) (f u) := by
              constructor
              · refine ⟨WithLp.ofLp u, ?_, ?_⟩
                · simpa using hun
                · exact dotProduct_comm _ _
              · rintro _ ⟨v, hv, rfl⟩
                have hh : f (WithLp.toLp p v) ≤ f u :=
                  hmax (show WithLp.toLp p v ∈ Metric.closedBall 0 1 by simpa using hv)
                simpa only [f, WithLp.ofLp_toLp, dotProduct_comm] using hh
            have hfu : f u = 1 := by rw [← hG i]; exact hgreat.csSup_eq.symm
            exact ⟨WithLp.ofLp u, by simpa using hun, hfu⟩
          have hDistSlack : ∀ z ∈ Xi M, ∀ i,
              ptDist p z (hyperplane M i) ≤ (((M.G *ᵥ z) i - M.g0 i : ℝ) : EReal) := by
            intro z hz i
            obtain ⟨u, hu, hui⟩ := hUnit i
            let s := (M.G *ᵥ z) i - M.g0 i
            have hs : 0 ≤ s := sub_nonneg.mpr (hz i)
            let y := z - s • u
            have hy : y ∈ hyperplane M i := by
              change M.G i ⬝ᵥ (z - s • u) = M.g0 i
              rw [dotProduct_sub, dotProduct_smul, hui, smul_eq_mul, mul_one]
              dsimp [s, mulVec]; ring
            have hn : ‖WithLp.toLp p (z - y)‖ ≤ s := by
              have he : z - y = s • u := by dsimp [y]; abel
              rw [he, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
              nlinarith
            calc
              ptDist p z (hyperplane M i) ≤ ((‖WithLp.toLp p (z - y)‖ : ℝ) : EReal) :=
                iInf_le_of_le y (iInf_le_of_le hy le_rfl)
              _ ≤ (s : EReal) := by exact_mod_cast hn
          have hTface : IsFaceOf T T := ⟨hTne, Or.inr (Or.inl rfl)⟩
          have hThetaOne : (1 : EReal) ≤ thetaPoly M p T := le_max_left _ _
          have hThetaFace : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F →
              ∀ i, (F ∩ hyperplane M i).Nonempty → thetaFace M p F i ≤ thetaPoly M p T := by
            intro F hF i hi
            unfold thetaPoly
            refine le_trans ?_ (le_max_right _ _)
            exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le i (le_iSup_of_le hi le_rfl)))
          have hThetaApprox : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F →
              ∀ i, (F ∩ hyperplane M i).Nonempty →
              ∀ b : ℝ, thetaPoly M p T < (b : EReal) →
              ∃ t : ℝ, 0 ≤ t ∧ t < b ∧ ∀ z ∈ F,
                ptDist p z (F ∩ hyperplane M i) ≤ (t : EReal) * ptDist p z (hyperplane M i) := by
            intro F hF i hi b hb
            have hh : thetaFace M p F i < (b : EReal) := (hThetaFace hF i hi).trans_lt hb
            obtain ⟨θ, ⟨t, ht, rfl, hbound⟩, hlt⟩ := sInf_lt_iff.mp hh
            exact ⟨t, ht, by exact_mod_cast hlt, hbound⟩
          have hBaseSlack : ∀ {F : Set (Fin d → ℝ)}, IsFaceOf T F →
              polyDim F ≤ minFaceDim T → ∀ z ∈ F, ∀ i,
              (M.G *ᵥ z) i ≠ M.g0 i → R ≤ (M.G *ᵥ z) i - M.g0 i := by
            intro F hF hdim z hz i hi
            by_cases hne : (F ∩ hyperplane M i).Nonempty
            · have hd : polyDim (F ∩ hyperplane M i) < polyDim F := by
                apply hDimCut (M.G i) (M.g0 i) hne Set.inter_subset_left
                · intro x hx; exact hx.2
                · exact ⟨z, hz, hi⟩
              have := hMinDim (hCut hF i hne)
              omega
            · have he : F ∩ hyperplane M i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
              exact_mod_cast (hRadDist hF z hz i he).trans (hDistSlack z (hTXi (hFaceSub hF hz)) i)
          have hcore : ∀ zhat ∈ T, ∃ zbar ∈ T,
              ‖WithLp.toLp p (zhat - zbar)‖ + ε ≤ lam * εbar ∧
              ∀ i, (M.G *ᵥ zbar) i ≠ M.g0 i →
                ‖WithLp.toLp p (zhat - zbar)‖ + ε ≤ lam * ((M.G *ᵥ zbar) i - M.g0 i) := by
            intro zhat hzhat
            by_cases hεpos : ε ≤ 0
            · refine ⟨zhat, hzhat, ?_, ?_⟩
              · simp only [sub_self]
                have : ‖WithLp.toLp p (0 : Fin d → ℝ)‖ = 0 := by simp
                rw [this]; nlinarith
              · intro i hi
                have hz : M.g0 i ≤ (M.G *ᵥ zhat) i := hTXi hzhat i
                have hpos : 0 < (M.G *ᵥ zhat) i - M.g0 i := lt_of_le_of_ne (by linarith) (fun h => hi (by linarith))
                simp only [sub_self]
                have : ‖WithLp.toLp p (0 : Fin d → ℝ)‖ = 0 := by simp
                rw [this]; nlinarith
            · rw [not_le] at hεpos
              by_cases htop : thetaPoly M p T = ⊤
              · have hgap : polyDim T - minFaceDim T = 0 := by
                  by_contra hn
                  have he : ε = 0 := by
                    dsimp [ε, epsThm3]
                    rw [htop, EReal.toReal_top]
                    simp [zero_pow hn]
                  linarith
                have he : ε = lam * R := by
                  dsimp [ε, epsThm3]
                  rw [hgap, pow_zero, one_mul]
                refine ⟨zhat, hzhat, ?_, ?_⟩
                · simpa [he] using mul_le_mul_of_nonneg_left hRbar hl0.le
                · intro i hi
                  have hs := hBaseSlack hTface (by omega) zhat hzhat i hi
                  simpa [he] using mul_le_mul_of_nonneg_left hs hl0.le
              · let θ : ℝ := (thetaPoly M p T).toReal
                have hθ1 : 1 ≤ θ := by
                  have := EReal.toReal_le_toReal hThetaOne (EReal.coe_ne_bot (1 : ℝ)) htop
                  simpa [θ] using this
                have hθ0 : 0 < θ := by linarith
                have hθcoe : (θ : EReal) = thetaPoly M p T :=
                  EReal.coe_toReal htop (ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 1) hThetaOne))
                let q : ℝ := lam / (2 * θ)
                have hq0 : 0 < q := div_pos hl0 (by positivity)
                have hq1 : q < 1 := (div_lt_one (by positivity : 0 < 2 * θ)).mpr (by linarith)
                have he : ε = q ^ (polyDim T - minFaceDim T) * lam * R := rfl
                have hRpos : 0 < R := by
                  have hc : 0 < q ^ (polyDim T - minFaceDim T) * lam := mul_pos (pow_pos hq0 _) hl0
                  rw [he] at hεpos
                  exact pos_of_mul_pos_right hεpos hc.le
                let a : ℕ → ℝ := fun k => q ^ (k - minFaceDim T) * lam * R
                have ha0 : ∀ k, 0 < a k := fun k => mul_pos (mul_pos (pow_pos hq0 _) hl0) hRpos
                have haR : ∀ k, a k ≤ lam * R := by
                  intro k
                  have hp : q ^ (k - minFaceDim T) ≤ 1 := pow_le_one₀ hq0.le hq1.le
                  dsimp [a]
                  nlinarith [mul_nonneg hl0.le hR0]
                have hanti : ∀ j k, j ≤ k → a k ≤ a j := by
                  intro j k hjk
                  have hp := pow_le_pow_of_le_one hq0.le hq1.le (Nat.sub_le_sub_right hjk (minFaceDim T))
                  dsimp [a]
                  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hl0.le) hR0
                have harec : ∀ k, minFaceDim T < k → lam * a (k - 1) = 2 * θ * a k := by
                  intro k hk
                  have hexp : k - minFaceDim T = (k - 1 - minFaceDim T) + 1 := by omega
                  dsimp [a]
                  rw [hexp, pow_succ]
                  dsimp [q]
                  field_simp
                have hind : ∀ k : ℕ, ∀ F : Set (Fin d → ℝ), IsFaceOf T F → polyDim F = k →
                    ∀ z ∈ F, ∃ zbar ∈ F,
                      ‖WithLp.toLp p (z - zbar)‖ + a k ≤ lam * εbar ∧
                      ∀ i, (M.G *ᵥ zbar) i ≠ M.g0 i →
                        ‖WithLp.toLp p (z - zbar)‖ + a k ≤ lam * ((M.G *ᵥ zbar) i - M.g0 i) := by
                  intro k
                  induction k using Nat.strong_induction_on with
                  | h k ih =>
                    intro F hF hk z hz
                    have hzXi : z ∈ Xi M := hTXi (hFaceSub hF hz)
                    by_cases hgood : ∀ i, (M.G *ᵥ z) i ≠ M.g0 i → a k ≤ lam * ((M.G *ᵥ z) i - M.g0 i)
                    · refine ⟨z, hz, ?_, ?_⟩
                      · have hh := (haR k).trans (mul_le_mul_of_nonneg_left hRbar hl0.le)
                        simpa using hh
                      · simpa using hgood
                    · push Not at hgood
                      obtain ⟨i, hi, hsmall⟩ := hgood
                      let s : ℝ := (M.G *ᵥ z) i - M.g0 i
                      have hs0 : 0 ≤ s := sub_nonneg.mpr (hzXi i)
                      have hs : lam * s < a k := hsmall
                      have hne : (F ∩ hyperplane M i).Nonempty := by
                        by_contra hn
                        have hdis := hRadDist hF z hz i (Set.not_nonempty_iff_eq_empty.mp hn)
                        have hslack : R ≤ s := by exact_mod_cast hdis.trans (hDistSlack z hzXi i)
                        have := haR k
                        nlinarith
                      let F' := F ∩ hyperplane M i
                      have hF' : IsFaceOf T F' := hCut hF i hne
                      have hdim : polyDim F' < k := by
                        rw [← hk]
                        apply hDimCut (M.G i) (M.g0 i) hne Set.inter_subset_left
                        · intro x hx; exact hx.2
                        · exact ⟨z, hz, hi⟩
                      have hkmin : minFaceDim T < k := lt_of_le_of_lt (hMinDim hF') hdim
                      have hb : θ < 2 * θ - lam := by linarith
                      have hbE : thetaPoly M p T < ((2 * θ - lam : ℝ) : EReal) := by
                        rw [← hθcoe]; exact_mod_cast hb
                      obtain ⟨t, ht0, htb, htbound⟩ := hThetaApprox hF i hne (2 * θ - lam) hbE
                      have hts : t * s < a (k - 1) - a k := by
                        have hbs : t * s ≤ (2 * θ - lam) * s := mul_le_mul_of_nonneg_right htb.le hs0
                        have hmul : (2 * θ - lam) * (lam * s) < (2 * θ - lam) * a k :=
                          mul_lt_mul_of_pos_left hs (by linarith)
                        have hr := harec k hkmin
                        nlinarith
                      have hdist : ptDist p z F' < (((a (k - 1) - a k : ℝ)) : EReal) := by
                        calc
                          ptDist p z F' ≤ (t : EReal) * ptDist p z (hyperplane M i) := htbound z hz
                          _ ≤ (t : EReal) * (s : EReal) := mul_le_mul_of_nonneg_left (hDistSlack z hzXi i) (by exact_mod_cast ht0)
                          _ < ((a (k - 1) - a k : ℝ) : EReal) := by rw [← EReal.coe_mul]; exact_mod_cast hts
                      obtain ⟨zcheck, hcheck⟩ := iInf_lt_iff.mp hdist
                      obtain ⟨hzcheck, hcheck⟩ := iInf_lt_iff.mp hcheck
                      have hnorm : ‖WithLp.toLp p (z - zcheck)‖ < a (k - 1) - a k := by exact_mod_cast hcheck
                      obtain ⟨zbar, hzbar, hb1, hb2⟩ := ih (polyDim F') hdim F' hF' rfl zcheck hzcheck
                      have ha' : a (k - 1) ≤ a (polyDim F') := hanti _ _ (by omega)
                      have htri : ‖WithLp.toLp p (z - zbar)‖ + a k ≤
                          ‖WithLp.toLp p (zcheck - zbar)‖ + a (polyDim F') := by
                        have heq : z - zbar = (z - zcheck) + (zcheck - zbar) := by abel
                        rw [heq, WithLp.toLp_add]
                        have := norm_add_le (WithLp.toLp p (z - zcheck)) (WithLp.toLp p (zcheck - zbar))
                        linarith
                      exact ⟨zbar, hzbar.1, htri.trans hb1, fun j hj => htri.trans (hb2 j hj)⟩
                obtain ⟨zbar, hzbar, hb1, hb2⟩ := hind (polyDim T) T hTface rfl zhat hzhat
                exact ⟨zbar, hzbar, by simpa only [a, ← he] using hb1, fun i hi => by
                  simpa only [a, ← he] using hb2 i hi⟩
          intro zhat hzhat
          obtain ⟨zbar, hzbarT, hb1, hb2⟩ := hcore zhat hzhat
          refine ⟨zbar, hzbarT, ?_⟩
          rintro ζ' ⟨hζ'b, hζ'Xi⟩
          have hζ'b' : ‖WithLp.toLp p (ζ' - zhat)‖ ≤ ε := hζ'b
          have htri : ‖WithLp.toLp p (ζ' - zbar)‖ ≤ ‖WithLp.toLp p (zhat - zbar)‖ + ε := by
            have : ζ' - zbar = (ζ' - zhat) + (zhat - zbar) := by abel
            rw [this, WithLp.toLp_add]
            linarith [norm_add_le (WithLp.toLp p (ζ' - zhat)) (WithLp.toLp p (zhat - zbar))]
          have hzbarXi : M.g0 ≤ M.G *ᵥ zbar := hTXi hzbarT
          have hζ'Xi' : M.g0 ≤ M.G *ᵥ ζ' := hζ'Xi
          refine ⟨lam⁻¹ • (ζ' - (1 - lam) • zbar), ⟨?_, ?_⟩, ?_⟩
          · show ‖WithLp.toLp p (lam⁻¹ • (ζ' - (1 - lam) • zbar) - zbar)‖ ≤ εbar
            have : lam⁻¹ • (ζ' - (1 - lam) • zbar) - zbar = lam⁻¹ • (ζ' - zbar) := by
              funext j
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              field_simp
              ring
            rw [this, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl0)]
            rw [inv_mul_le_iff₀ hl0]
            linarith
          · show M.g0 ≤ M.G *ᵥ (lam⁻¹ • (ζ' - (1 - lam) • zbar))
            intro i
            rw [mulVec_smul, mulVec_sub, mulVec_smul]
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            rw [le_inv_mul_iff₀ hl0]
            have hz := hzbarXi i
            have hζ := hζ'Xi' i
            by_cases hact : (M.G *ᵥ zbar) i = M.g0 i
            · rw [hact]; nlinarith
            · have h2 := hb2 i hact
              have hH := hHold i (zbar - ζ')
              have : M.G i ⬝ᵥ (zbar - ζ') = (M.G *ᵥ zbar) i - (M.G *ᵥ ζ') i := by
                simp [mulVec, dotProduct_sub]
              rw [this] at hH
              have hn : ‖WithLp.toLp p (zbar - ζ')‖ = ‖WithLp.toLp p (ζ' - zbar)‖ := by
                rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
              rw [hn] at hH
              nlinarith
          · show lam • (lam⁻¹ • (ζ' - (1 - lam) • zbar)) + (1 - lam) • zbar = ζ'
            rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul, sub_add_cancel]
