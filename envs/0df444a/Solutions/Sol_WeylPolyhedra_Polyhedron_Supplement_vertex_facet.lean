-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.Supplement.vertex_facet
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:15.279133+00:00
-- url     : https://prove2.me/submissions/1dbadd0b-576d-447d-be7e-134da2313b52

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_Vertex

open WeylPolyhedra
open WeylPolyhedra.Polyhedron
open WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §4 I, p. 302, the unnumbered Satz, in affine form (`R̄_{n-1} = ℝᵐ`,
`m = n - 1`, a point `x` standing for `(x, -1)`). Let `S ⊆ ℝᵐ` be a finite non-degenerate point
system (affine span the whole space), `H` its convex polyhedron, facets the extreme supports
`(a, a₀)` of `S` and vertices as in `IsVertex`.
1. Through every vertex `v` of `H` pass at least `n - 1 = m` independent facets: `m` facets,
   linearly independent as vectors `(a, a₀) ∈ ℝᵐ × ℝ`, with `a ⬝ᵥ v - a₀ = 0`.
2. Every facet `(a, a₀)` contains at least `n - 1 = m` independent vertices: `m` affinely
   independent vertices `v` (their homogenizations `(v, -1)` linearly independent) with
   `a ⬝ᵥ v - a₀ = 0`. -/
theorem solution {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) :
    (∀ v : Fin m → ℝ, IsVertex S v →
        ∃ F : Finset ((Fin m → ℝ) × ℝ), F.card = m ∧
          (∀ p ∈ F, IsExtremeAffineSupport S p.1 p.2) ∧
          LinearIndependent ℝ (fun p : F => (p : (Fin m → ℝ) × ℝ)) ∧
          ∀ p ∈ F, p.1 ⬝ᵥ v - p.2 = 0) ∧
      (∀ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀ →
        ∃ V : Finset (Fin m → ℝ), V.card = m ∧
          AffineIndependent ℝ (fun v : V => (v : Fin m → ℝ)) ∧
          ∀ v ∈ V, IsVertex S v ∧ a ⬝ᵥ v - a₀ = 0) := by
            classical
            refine ⟨fun v hv => hv.2, ?_⟩
            -- the pairing
            let B : LinearMap.BilinForm ℝ ((Fin m → ℝ) × ℝ) :=
              LinearMap.mk₂ ℝ (fun x y => x.1 ⬝ᵥ y.1 + x.2 * y.2)
                (by intro x y z; simp [add_dotProduct]; ring)
                (by intro c x y; simp [smul_dotProduct]; ring)
                (by intro x y z; simp [dotProduct_add]; ring)
                (by intro c x y; simp [dotProduct_smul]; ring)
            have hB : ∀ x y, B x y = x.1 ⬝ᵥ y.1 + x.2 * y.2 := fun x y => rfl
            have hBsymm : ∀ x y, B x y = B y x := by
              intro x y; rw [hB, hB, dotProduct_comm, mul_comm]
            have hBrefl : B.IsRefl := fun x y h => by rw [hBsymm]; exact h
            have hsep : ∀ x, (∀ y, B x y = 0) → x = 0 := by
              intro x hx
              have h := hx x
              rw [hB] at h
              have h1 : 0 ≤ x.1 ⬝ᵥ x.1 := by
                simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
              have h2 : x.1 ⬝ᵥ x.1 = 0 := by nlinarith [mul_self_nonneg x.2]
              have h3 : x.2 = 0 := by nlinarith [mul_self_nonneg x.2]
              rw [dotProduct_self_eq_zero] at h2
              exact Prod.ext h2 h3
            have hBnd : B.Nondegenerate :=
              ⟨fun x hx => hsep x hx, fun y hy => hsep y (fun x => by rw [hBsymm]; exact hy x)⟩
            let g : (Fin m → ℝ) → (Fin m → ℝ) × ℝ := fun s => (s, -1)
            have hBg : ∀ α s, B α (g s) = α.1 ⬝ᵥ s - α.2 := by
              intro α s; rw [hB]; simp [g]; ring
            let e : (Fin m → ℝ) × ℝ := (0, -1)
            have hBe : ∀ s, B e (g s) = 1 := by intro s; rw [hBg]; simp [e]
            have hginj : Function.Injective g := fun x y h => congrArg Prod.fst h
            -- vanishing on all of S forces zero
            have hzero : ∀ β : (Fin m → ℝ) × ℝ, (∀ s ∈ S, B β (g s) = 0) → β = 0 := by
              intro β hβ
              let f : (Fin m → ℝ) →ᵃ[ℝ] ℝ :=
                ((B (β.1, 0)).comp (LinearMap.inl ℝ (Fin m → ℝ) ℝ)).toAffineMap - AffineMap.const ℝ (Fin m → ℝ) β.2
              have hf : ∀ x, f x = β.1 ⬝ᵥ x - β.2 := by intro x; simp [f, hB]
              have hfz : f = AffineMap.const ℝ (Fin m → ℝ) (0:ℝ) := by
                apply AffineMap.ext_on hS
                intro x hx
                simp only [AffineMap.const_apply, hf]
                rw [← hBg]; exact hβ x hx
              have h0 : ∀ x, β.1 ⬝ᵥ x - β.2 = 0 := by
                intro x; rw [← hf, hfz]; rfl
              have h2 : β.2 = 0 := by have := h0 0; simpa using this
              have h1 : β.1 = 0 := by
                have := h0 β.1
                rw [h2, sub_zero, dotProduct_self_eq_zero] at this; exact this
              exact Prod.ext h1 h2
            -- linear independence of homogenizations ↔ affine independence
            have hLA : ∀ (T : Finset (Fin m → ℝ)),
                LinearIndependent ℝ (fun t : T => g t) → AffineIndependent ℝ (fun t : T => (t : Fin m → ℝ)) := by
              intro T hT
              rw [linearIndependent_iff'] at hT
              intro s w hw hv
              rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w _ hw 0,
                Finset.weightedVSubOfPoint_apply] at hv
              apply hT s w
              simp only [vsub_eq_sub, sub_zero] at hv
              refine Prod.ext ?_ ?_
              · rw [Prod.fst_sum]; simpa [g] using hv
              · rw [Prod.snd_sum]; simp [g, hw]
            have hAL : ∀ (T : Finset (Fin m → ℝ)),
                AffineIndependent ℝ (fun t : T => (t : Fin m → ℝ)) → LinearIndependent ℝ (fun t : T => g t) := by
              intro T hT
              rw [linearIndependent_iff']
              intro s w hv
              have h1 := congrArg Prod.fst hv
              have h2 := congrArg Prod.snd hv
              rw [Prod.fst_sum] at h1
              rw [Prod.snd_sum] at h2
              simp [g] at h1 h2
              apply hT s w h2
              rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w _ h2 0,
                Finset.weightedVSubOfPoint_apply]
              simpa using h1
            have hBsub : ∀ x y z, B (x - y) z = B x z - B y z := by intro x y z; simp
            have hBsmul : ∀ (c : ℝ) x z, B (c • x) z = c * B x z := by intro c x z; simp
            have hBadd : ∀ x y z, B (x + y) z = B x z + B y z := by intro x y z; simp
            have hfinE : Module.finrank ℝ ((Fin m → ℝ) × ℝ) = m + 1 := by simp
            have hortho : ∀ (X : Set ((Fin m → ℝ) × ℝ)) x, (∀ y ∈ X, B y x = 0) →
                x ∈ B.orthogonal (Submodule.span ℝ X) := by
              intro X x hx
              rw [LinearMap.BilinForm.mem_orthogonal_iff]
              intro n hn
              induction hn using Submodule.span_induction with
              | mem y hy => exact hx y hy
              | zero => simp
              | add y z _ _ h1 h2 => rw [hBadd, h1, h2, add_zero]
              | smul c y _ h => rw [hBsmul, h, mul_zero]
            have horthoE : ∀ (X : Set ((Fin m → ℝ) × ℝ)) x, x ∈ B.orthogonal (Submodule.span ℝ X) →
                ∀ y ∈ X, B y x = 0 := by
              intro X x hx y hy
              rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
              exact hx y (Submodule.subset_span hy)
            -- extraction of independent points
            have hextract : ∀ (P : Finset (Fin m → ℝ)),
                m ≤ Module.finrank ℝ (Submodule.span ℝ (g '' (P : Set (Fin m → ℝ)))) →
                ∃ T ⊆ P, T.card = m ∧ LinearIndependent ℝ (fun t : T => g t) := by
              intro P hP
              obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (g '' (P : Set (Fin m → ℝ)))
              let T0 := P.filter (fun s => g s ∈ b)
              have hT0li : LinearIndependent ℝ (fun t : T0 => g t) := by
                have := hbli.comp (fun t : T0 => (⟨g t, (Finset.mem_filter.1 t.2).2⟩ : b))
                  (by intro x y h; apply Subtype.ext; apply hginj; simpa using congrArg Subtype.val h)
                exact this
              have hrange : Set.range (fun t : T0 => g t) = b := by
                ext y; constructor
                · rintro ⟨t, rfl⟩; exact (Finset.mem_filter.1 t.2).2
                · intro hy
                  obtain ⟨s, hs, rfl⟩ := hbsub hy
                  exact ⟨⟨s, Finset.mem_filter.2 ⟨hs, hy⟩⟩, rfl⟩
              have hcard : m ≤ T0.card := by
                have := finrank_span_eq_card hT0li
                rw [hrange, hbspan, Fintype.card_coe] at this
                omega
              obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
              refine ⟨T, hTsub.trans (Finset.filter_subset _ _), hTcard, ?_⟩
              exact hT0li.comp (fun t : T => (⟨t, hTsub t.2⟩ : T0))
                (by intro x y h; apply Subtype.ext; simpa using congrArg Subtype.val h)
            let Fac : (Fin m → ℝ) × ℝ → Prop := fun α => IsExtremeAffineSupport S α.1 α.2
            let Fsp : (Fin m → ℝ) × ℝ → Submodule ℝ ((Fin m → ℝ) × ℝ) := fun β =>
              Submodule.span ℝ {α | Fac α ∧ ∀ s ∈ S, B β (g s) = 0 → B α (g s) = 0}
            have hne : ∀ α : (Fin m → ℝ) × ℝ, α ≠ 0 ↔ (α.1 ≠ 0 ∨ α.2 ≠ 0) := by
              intro α; constructor
              · intro h; by_contra h'; push_neg at h'; exact h (Prod.ext h'.1 h'.2)
              · rintro h rfl; simp at h
            have hFacOf : ∀ β : (Fin m → ℝ) × ℝ, β ≠ 0 → (∀ s ∈ S, 0 ≤ B β (g s)) →
                (∃ T ⊆ S, T.card = m ∧ LinearIndependent ℝ (fun t : T => g t) ∧ ∀ t ∈ T, B β (g t) = 0) →
                Fac β := by
              rintro β h0 hnn ⟨T, hT, hc, hli, ht⟩
              refine ⟨(hne β).1 h0, fun s hs => by rw [← hBg]; exact hnn s hs, T, hT, hc, hLA T hli,
                fun t htT => by rw [← hBg]; exact ht t htT⟩
            have hL : ∀ n, ∀ β : (Fin m → ℝ) × ℝ, (S.filter (fun s => B β (g s) ≠ 0)).card = n →
                β ≠ 0 → (∀ s ∈ S, 0 ≤ B β (g s)) →
                ∀ γ, (∀ s ∈ S, B β (g s) = 0 → B γ (g s) = 0) → γ ∈ Fsp β := by
              intro n
              induction n using Nat.strong_induction_on with
              | _ n IH =>
              intro β hn hβ0 hβ γ hγ
              have hmono : ∀ β', (∀ s ∈ S, B β (g s) = 0 → B β' (g s) = 0) → Fsp β' ≤ Fsp β := by
                intro β' hb
                apply Submodule.span_mono
                rintro α ⟨hα, h⟩
                exact ⟨hα, fun s hs h0 => h s hs (hb s hs h0)⟩
              have hrot : ∀ γ, (∀ s ∈ S, B β (g s) = 0 → B γ (g s) = 0) → (∀ c : ℝ, γ ≠ c • β) →
                  β ∈ Fsp β ∧ γ ∈ Fsp β := by
                intro γ hγ hγc
                let S' := S.filter (fun s => B β (g s) ≠ 0)
                have hS'ne : S'.Nonempty := by
                  by_contra h
                  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
                  exact hβ0 (hzero β (fun s hs => by simpa using h hs))
                have hpos : ∀ s ∈ S', 0 < B β (g s) := by
                  intro s hs
                  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
                  exact lt_of_le_of_ne (hβ s hs1) (Ne.symm hs2)
                let r : (Fin m → ℝ) → ℝ := fun s => B γ (g s) / B β (g s)
                obtain ⟨smin, hsmin, hmin⟩ := Finset.exists_min_image S' r hS'ne
                obtain ⟨smax, hsmax, hmax⟩ := Finset.exists_max_image S' r hS'ne
                let γ₁ := γ - r smin • β
                let γ₂ := r smax • β - γ
                have hγ₁ : ∀ s, B γ₁ (g s) = B γ (g s) - r smin * B β (g s) := by
                  intro s; simp [γ₁]
                have hγ₂ : ∀ s, B γ₂ (g s) = r smax * B β (g s) - B γ (g s) := by
                  intro s; simp [γ₂]
                have hγ₁nn : ∀ s ∈ S, 0 ≤ B γ₁ (g s) := by
                  intro s hs
                  rw [hγ₁]
                  by_cases h0 : B β (g s) = 0
                  · rw [h0, hγ s hs h0]; simp
                  · have hs' : s ∈ S' := Finset.mem_filter.2 ⟨hs, h0⟩
                    have := hmin s hs'
                    have hp := hpos s hs'
                    have : r smin * B β (g s) ≤ B γ (g s) := by
                      have h' : r smin ≤ B γ (g s) / B β (g s) := this
                      rwa [le_div_iff₀ hp] at h'
                    linarith
                have hγ₂nn : ∀ s ∈ S, 0 ≤ B γ₂ (g s) := by
                  intro s hs
                  rw [hγ₂]
                  by_cases h0 : B β (g s) = 0
                  · rw [h0, hγ s hs h0]; simp
                  · have hs' : s ∈ S' := Finset.mem_filter.2 ⟨hs, h0⟩
                    have := hmax s hs'
                    have hp := hpos s hs'
                    have : B γ (g s) ≤ r smax * B β (g s) := by
                      have h' : B γ (g s) / B β (g s) ≤ r smax := this
                      rwa [div_le_iff₀ hp] at h'
                    linarith
                have hγ₁0 : γ₁ ≠ 0 := by
                  intro h; apply hγc (r smin); rw [← sub_eq_zero]; exact h
                have hγ₂0 : γ₂ ≠ 0 := by
                  intro h; apply hγc (r smax); rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]; exact h
                have hz1 : B γ₁ (g smin) = 0 := by
                  rw [hγ₁]
                  have hp := hpos smin hsmin
                  simp only [r]; field_simp; ring
                have hz2 : B γ₂ (g smax) = 0 := by
                  rw [hγ₂]
                  have hp := hpos smax hsmax
                  simp only [r]; field_simp; ring
                have htight : ∀ γ', (∀ s ∈ S, B β (g s) = 0 → B γ' (g s) = 0) → ∀ s0 ∈ S',
                    B γ' (g s0) = 0 → (S.filter (fun s => B γ' (g s) ≠ 0)).card < n := by
                  intro γ' hγ' s0 hs0 hz
                  rw [← hn]
                  apply Finset.card_lt_card
                  rw [Finset.ssubset_iff_of_subset]
                  · exact ⟨s0, hs0, fun h => (Finset.mem_filter.1 h).2 hz⟩
                  · intro s hs
                    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
                    exact Finset.mem_filter.2 ⟨hs1, fun h => hs2 (hγ' s hs1 h)⟩
                have hγ₁t : ∀ s ∈ S, B β (g s) = 0 → B γ₁ (g s) = 0 := by
                  intro s hs h; rw [hγ₁, h, hγ s hs h]; simp
                have hγ₂t : ∀ s ∈ S, B β (g s) = 0 → B γ₂ (g s) = 0 := by
                  intro s hs h; rw [hγ₂, h, hγ s hs h]; simp
                have hm1 : γ₁ ∈ Fsp β := hmono γ₁ hγ₁t
                  (IH _ (htight γ₁ hγ₁t smin hsmin hz1) γ₁ rfl hγ₁0 hγ₁nn γ₁ (fun s _ h => h))
                have hm2 : γ₂ ∈ Fsp β := hmono γ₂ hγ₂t
                  (IH _ (htight γ₂ hγ₂t smax hsmax hz2) γ₂ rfl hγ₂0 hγ₂nn γ₂ (fun s _ h => h))
                have hsum : γ₁ + γ₂ = (r smax - r smin) • β := by
                  simp only [γ₁, γ₂, sub_smul]; abel
                have hdiff : r smax - r smin ≠ 0 := by
                  intro h
                  rw [h, zero_smul] at hsum
                  apply hγ₁0
                  apply hzero
                  intro s hs
                  have e1 := hγ₁nn s hs
                  have e2 := hγ₂nn s hs
                  have : B (γ₁ + γ₂) (g s) = 0 := by rw [hsum]; simp
                  rw [hBadd] at this
                  linarith
                have hβm : β ∈ Fsp β := by
                  have : β = (r smax - r smin)⁻¹ • (γ₁ + γ₂) := by
                    rw [hsum, smul_smul, inv_mul_cancel₀ hdiff, one_smul]
                  have key : (r smax - r smin)⁻¹ • (γ₁ + γ₂) ∈ Fsp β :=
                    Submodule.smul_mem _ _ (Submodule.add_mem _ hm1 hm2)
                  rw [← this] at key; exact key
                refine ⟨hβm, ?_⟩
                have : γ = γ₁ + r smin • β := by simp [γ₁]
                rw [this]
                exact Submodule.add_mem _ hm1 (Submodule.smul_mem _ _ hβm)
              by_cases hc : ∃ c : ℝ, γ = c • β
              · obtain ⟨c, rfl⟩ := hc
                apply Submodule.smul_mem
                by_cases hfac : Fac β
                · exact Submodule.subset_span ⟨hfac, fun s _ h => h⟩
                · by_contra hnot
                  have hall : ∀ γ', (∀ s ∈ S, B β (g s) = 0 → B γ' (g s) = 0) → ∃ c : ℝ, γ' = c • β := by
                    intro γ' hγ'
                    by_contra h; push_neg at h
                    exact hnot (hrot γ' hγ' h).1
                  let D := S.filter (fun s => B β (g s) = 0)
                  let W := Submodule.span ℝ (g '' (D : Set (Fin m → ℝ)))
                  have hle : B.orthogonal W ≤ Submodule.span ℝ {β} := by
                    intro x hx
                    have := horthoE _ x hx
                    obtain ⟨c, rfl⟩ := hall x (fun s hs h0 => by
                      rw [← hBsymm]; exact this (g s) ⟨s, Finset.mem_filter.2 ⟨hs, h0⟩, rfl⟩)
                    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self β)
                  have h1 := Submodule.finrank_mono hle
                  have h2 := LinearMap.BilinForm.finrank_orthogonal hBnd W
                  have h3 : Module.finrank ℝ (Submodule.span ℝ {β}) ≤ 1 := by
                    have := finrank_span_le_card (R := ℝ) ({β} : Set ((Fin m → ℝ) × ℝ)); simpa using this
                  have h4 := Submodule.finrank_le W
                  obtain ⟨T, hTD, hTc, hTli⟩ := hextract D
                    (by rw [hfinE] at h2 h4; show m ≤ Module.finrank ℝ W; omega)
                  exact hfac (hFacOf β hβ0 hβ ⟨T, hTD.trans (Finset.filter_subset _ _), hTc, hTli,
                    fun t ht => (Finset.mem_filter.1 (hTD ht)).2⟩)
              · push_neg at hc
                exact (hrot γ hγ hc).2
            have hL' : ∀ β : (Fin m → ℝ) × ℝ, β ≠ 0 → (∀ s ∈ S, 0 ≤ B β (g s)) →
                ∀ γ, (∀ s ∈ S, B β (g s) = 0 → B γ (g s) = 0) → γ ∈ Fsp β :=
              fun β => hL _ β rfl
            -- exposed points are vertices
            have hgood : ∀ s ∈ S, ∀ β : (Fin m → ℝ) × ℝ, β ≠ 0 → (∀ x ∈ S, 0 ≤ B β (g x)) →
                B β (g s) = 0 → (∀ x ∈ S, B β (g x) = 0 → x = s) → IsVertex S s := by
              intro s hs β hβ0 hβ hβs hβu
              refine ⟨fun a a₀ ha => ha.2.1 s hs, ?_⟩
              let A := {α | Fac α ∧ ∀ x ∈ S, B β (g x) = 0 → B α (g x) = 0}
              have hA : ∀ α ∈ A, B α (g s) = 0 := fun α hα => hα.2 s hs hβs
              have heq : Fsp β = B.orthogonal (Submodule.span ℝ {g s}) := by
                apply le_antisymm
                · apply Submodule.span_le.2
                  intro α hα
                  apply hortho
                  intro y hy
                  rw [Set.mem_singleton_iff] at hy
                  rw [hy, hBsymm]; exact hA α hα
                · intro x hx
                  apply hL' β hβ0 hβ x
                  intro y hy h0
                  rw [hβu y hy h0, hBsymm]
                  exact horthoE _ x hx (g s) rfl
              have hgs : g s ≠ 0 := by intro h; have := congrArg Prod.snd h; simp [g] at this
              have hfin : Module.finrank ℝ (Fsp β) = m := by
                rw [heq, LinearMap.BilinForm.finrank_orthogonal hBnd, finrank_span_singleton hgs, hfinE]
                simp
              obtain ⟨b, hbA, hbspan, hbli⟩ := exists_linearIndependent ℝ A
              have hbfin : b.Finite := hbli.setFinite
              haveI := hbfin.fintype
              have hcard := finrank_span_set_eq_card (R := ℝ) (s := b) hbli
              rw [hbspan] at hcard
              refine ⟨b.toFinset, ?_, ?_, ?_, ?_⟩
              · rw [← hcard]; exact hfin
              · intro p hp
                exact (hbA (Set.mem_toFinset.1 hp)).1
              · exact hbli.comp (fun p : b.toFinset => (⟨p, Set.mem_toFinset.1 p.2⟩ : b))
                  (by intro x y h; apply Subtype.ext; simpa using congrArg Subtype.val h)
              · intro p hp
                rw [← hBg]; exact hA p (hbA (Set.mem_toFinset.1 hp))
            -- face lemma
            have hface : ∀ β : (Fin m → ℝ) × ℝ, β ≠ 0 → (∀ s ∈ S, 0 ≤ B β (g s)) →
                ∀ δ, (∀ x ∈ S, B β (g x) = 0 → 0 ≤ B δ (g x)) →
                (∃ x ∈ S, B β (g x) = 0 ∧ 0 < B δ (g x)) →
                ∃ β' : (Fin m → ℝ) × ℝ, β' ≠ 0 ∧ (∀ s ∈ S, 0 ≤ B β' (g s)) ∧
                  ∀ x ∈ S, (B β' (g x) = 0 ↔ B β (g x) = 0 ∧ B δ (g x) = 0) := by
              intro β hβ0 hβ δ hδ ⟨x0, hx0, hx0β, hx0δ⟩
              let K : ℝ := ∑ x ∈ S, |B δ (g x)| / B β (g x) + 1
              have hK : ∀ x ∈ S, |B δ (g x)| / B β (g x) + 1 ≤ K := by
                intro x hx
                have := Finset.single_le_sum (f := fun x => |B δ (g x)| / B β (g x))
                  (fun y hy => div_nonneg (abs_nonneg _) (hβ y hy)) hx
                simp only [K]; linarith
              have hval : ∀ x, B (K • β + δ) (g x) = K * B β (g x) + B δ (g x) := by
                intro x; rw [hBadd, hBsmul]
              have hposx : ∀ x ∈ S, B β (g x) ≠ 0 → 0 < B (K • β + δ) (g x) := by
                intro x hx h0
                have hp : 0 < B β (g x) := lt_of_le_of_ne (hβ x hx) (Ne.symm h0)
                have h1 := hK x hx
                have h2 : (|B δ (g x)| / B β (g x) + 1) * B β (g x) ≤ K * B β (g x) :=
                  mul_le_mul_of_nonneg_right h1 hp.le
                have h3 : (|B δ (g x)| / B β (g x) + 1) * B β (g x) = |B δ (g x)| + B β (g x) := by
                  field_simp
                have h4 := neg_abs_le (B δ (g x))
                rw [hval]; linarith
              refine ⟨K • β + δ, ?_, ?_, ?_⟩
              · intro h
                have := hval x0
                rw [h, hx0β] at this
                simp at this; linarith
              · intro x hx
                by_cases h0 : B β (g x) = 0
                · rw [hval, h0]; simpa using hδ x hx h0
                · exact (hposx x hx h0).le
              · intro x hx
                by_cases h0 : B β (g x) = 0
                · rw [hval, h0]; simp
                · constructor
                  · intro h; exact absurd h (hposx x hx h0).ne'
                  · intro h; exact absurd h.1 h0
            have hexist : ∀ n, ∀ β : (Fin m → ℝ) × ℝ, (S.filter (fun s => B β (g s) = 0)).card = n →
                β ≠ 0 → (∀ s ∈ S, 0 ≤ B β (g s)) → (∃ x ∈ S, B β (g x) = 0) →
                ∃ x ∈ S, B β (g x) = 0 ∧ IsVertex S x := by
              intro n
              induction n using Nat.strong_induction_on with
              | _ n IH =>
              intro β hn hβ0 hβ ⟨x0, hx0, hx0β⟩
              by_cases hu : ∀ y ∈ S, B β (g y) = 0 → y = x0
              · exact ⟨x0, hx0, hx0β, hgood x0 hx0 β hβ0 hβ hx0β hu⟩
              push_neg at hu
              obtain ⟨y, hy, hyβ, hyx⟩ := hu
              let D := S.filter (fun s => B β (g s) = 0)
              have hDne : D.Nonempty := ⟨x0, Finset.mem_filter.2 ⟨hx0, hx0β⟩⟩
              let l : (Fin m → ℝ) × ℝ := (x0 - y, 0)
              obtain ⟨z0, hz0, hzmin⟩ := Finset.exists_min_image D (fun s => B l (g s)) hDne
              let δ := l - B l (g z0) • e
              have hδ : ∀ s, B δ (g s) = B l (g s) - B l (g z0) := by
                intro s; simp only [δ]; rw [hBsub, hBsmul, hBe]; ring
              have hδnn : ∀ x ∈ S, B β (g x) = 0 → 0 ≤ B δ (g x) := by
                intro x hx h0
                rw [hδ]; have := hzmin x (Finset.mem_filter.2 ⟨hx, h0⟩); linarith
              have hl : B l (g x0) - B l (g y) = (x0 - y) ⬝ᵥ (x0 - y) := by
                rw [hBg, hBg]; simp only [l, dotProduct_sub, sub_dotProduct]; ring
              have hlpos : 0 < (x0 - y) ⬝ᵥ (x0 - y) := by
                have h1 : 0 ≤ (x0 - y) ⬝ᵥ (x0 - y) := by
                  simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
                refine lt_of_le_of_ne h1 (Ne.symm ?_)
                rw [Ne, dotProduct_self_eq_zero, sub_eq_zero]; exact Ne.symm hyx
              have hsome : ∃ x ∈ S, B β (g x) = 0 ∧ 0 < B δ (g x) := by
                by_cases h : B δ (g x0) = 0
                · refine ⟨y, hy, hyβ, ?_⟩
                  have := hδnn y hy hyβ
                  rw [hδ] at h ⊢; rw [hδ] at this
                  linarith
                · exact ⟨x0, hx0, hx0β, lt_of_le_of_ne (hδnn x0 hx0 hx0β) (Ne.symm h)⟩
              obtain ⟨x1, hx1, hx1β, hx1δ⟩ := hsome
              obtain ⟨β', hβ'0, hβ', hiff⟩ := hface β hβ0 hβ δ hδnn ⟨x1, hx1, hx1β, hx1δ⟩
              have hz0S := Finset.mem_filter.1 hz0
              have hlt : (S.filter (fun s => B β' (g s) = 0)).card < n := by
                rw [← hn]
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset]
                · refine ⟨x1, Finset.mem_filter.2 ⟨hx1, hx1β⟩, fun h => ?_⟩
                  have := ((hiff x1 hx1).1 (Finset.mem_filter.1 h).2).2
                  linarith
                · intro s hs
                  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
                  exact Finset.mem_filter.2 ⟨hs1, ((hiff s hs1).1 hs2).1⟩
              obtain ⟨x, hx, hxβ', hxv⟩ := IH _ hlt β' rfl hβ'0 hβ'
                ⟨z0, hz0S.1, (hiff z0 hz0S.1).2 ⟨hz0S.2, by rw [hδ]; ring⟩⟩
              exact ⟨x, hx, ((hiff x hx).1 hxβ').1, hxv⟩
            -- part 2
            intro a a₀ ha
            let β : (Fin m → ℝ) × ℝ := (a, a₀)
            have hβ0 : β ≠ 0 := (hne β).2 ha.1
            have hβ : ∀ s ∈ S, 0 ≤ B β (g s) := fun s hs => by rw [hBg]; exact ha.2.1 s hs
            obtain ⟨T, hTS, hTc, hTai, hTt⟩ := ha.2.2
            let D := S.filter (fun s => B β (g s) = 0)
            let Gd := D.filter (fun s => IsVertex S s)
            have hDT : T ⊆ D := fun t ht => Finset.mem_filter.2 ⟨hTS ht, by rw [hBg]; exact hTt t ht⟩
            have hspan : Submodule.span ℝ (g '' (D : Set (Fin m → ℝ))) ≤
                Submodule.span ℝ (g '' (Gd : Set (Fin m → ℝ))) := by
              have hle : B.orthogonal (Submodule.span ℝ (g '' (Gd : Set (Fin m → ℝ)))) ≤
                  B.orthogonal (Submodule.span ℝ (g '' (D : Set (Fin m → ℝ)))) := by
                intro γ hγ
                have hγG := horthoE _ γ hγ
                apply hortho
                rintro _ ⟨x1, hx1, rfl⟩
                by_contra hne1
                rw [hBsymm] at hne1
                have hGz : ∀ x ∈ Gd, B γ (g x) = 0 := fun x hx => by
                  rw [← hBsymm]; exact hγG (g x) ⟨x, hx, rfl⟩
                obtain ⟨γ', hγ'G, hγ'x1⟩ : ∃ γ' : (Fin m → ℝ) × ℝ, (∀ x ∈ Gd, B γ' (g x) = 0) ∧
                    B γ' (g x1) < 0 := by
                  rcases lt_or_gt_of_ne hne1 with h | h
                  · exact ⟨γ, hGz, h⟩
                  · refine ⟨-γ, fun x hx => by simp [hGz x hx], by simp; linarith⟩
                have hDne : D.Nonempty := ⟨x1, hx1⟩
                obtain ⟨z0, hz0, hzmin⟩ := Finset.exists_min_image D (fun s => B γ' (g s)) hDne
                have hμ : B γ' (g z0) < 0 := lt_of_le_of_lt (hzmin x1 hx1) hγ'x1
                let δ := γ' - B γ' (g z0) • e
                have hδ : ∀ s, B δ (g s) = B γ' (g s) - B γ' (g z0) := by
                  intro s; simp only [δ]; rw [hBsub, hBsmul, hBe]; ring
                have hδnn : ∀ x ∈ S, B β (g x) = 0 → 0 ≤ B δ (g x) := by
                  intro x hx h0
                  rw [hδ]; have := hzmin x (Finset.mem_filter.2 ⟨hx, h0⟩); linarith
                have hz0S := Finset.mem_filter.1 hz0
                obtain ⟨y, hy, hyβ, hyv⟩ := hexist _ β rfl hβ0 hβ ⟨z0, hz0S.1, hz0S.2⟩
                have hyG : y ∈ Gd := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hy, hyβ⟩, hyv⟩
                obtain ⟨β', hβ'0, hβ', hiff⟩ := hface β hβ0 hβ δ hδnn
                  ⟨y, hy, hyβ, by rw [hδ, hγ'G y hyG]; linarith⟩
                obtain ⟨x, hx, hxβ', hxv⟩ := hexist _ β' rfl hβ'0 hβ'
                  ⟨z0, hz0S.1, (hiff z0 hz0S.1).2 ⟨hz0S.2, by rw [hδ]; ring⟩⟩
                obtain ⟨hxβ, hxδ⟩ := (hiff x hx).1 hxβ'
                have hxG : x ∈ Gd := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hx, hxβ⟩, hxv⟩
                rw [hδ, hγ'G x hxG] at hxδ
                linarith
              have := LinearMap.BilinForm.orthogonal_le (B := B) hle
              rwa [LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl,
                LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl] at this
            have hTli := hAL T hTai
            have hfr : m ≤ Module.finrank ℝ (Submodule.span ℝ (g '' (Gd : Set (Fin m → ℝ)))) := by
              have h1 := finrank_span_eq_card hTli
              rw [Fintype.card_coe, hTc] at h1
              have h2 : Submodule.span ℝ (Set.range (fun t : T => g t)) ≤
                  Submodule.span ℝ (g '' (D : Set (Fin m → ℝ))) := by
                apply Submodule.span_mono
                rintro _ ⟨t, rfl⟩
                exact ⟨t, hDT t.2, rfl⟩
              have := Submodule.finrank_mono (h2.trans hspan)
              omega
            obtain ⟨V, hVG, hVc, hVli⟩ := hextract Gd hfr
            refine ⟨V, hVc, hLA V hVli, fun v hv => ?_⟩
            have h1 := Finset.mem_filter.1 (hVG hv)
            have h2 := Finset.mem_filter.1 h1.1
            refine ⟨h1.2, ?_⟩
            have := h2.2
            rw [hBg] at this
            exact this
