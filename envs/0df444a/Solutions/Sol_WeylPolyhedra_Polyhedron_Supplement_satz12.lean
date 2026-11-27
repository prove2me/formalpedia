-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.Supplement.satz12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:49.299889+00:00
-- url     : https://prove2.me/submissions/ecdcc723-81b2-4531-a909-b4eb8fae189e

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

open WeylPolyhedra
open WeylPolyhedra.Polyhedron
open WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 12, for the convex pyramid of `S`, under the hypotheses of
Satz 9 kept for the rest of §3 (`S` non-degenerate, `(S)` with an inner point `ξ⁰`). The extreme
edges of the pyramid are the rays of the extreme solutions `a′` of `Σ` (`sPrimeSet S`, by
Satz 10 a selection among the points of `S`); its support planes are the supports `ξ` of `S`
(`ξ ≠ 0`, `ξ ⬝ᵥ s ≥ 0` on `S`) and its extreme support planes the extreme supports of `S`.
1. Through every extreme edge `a′` pass `n - 1` linearly independent support planes.
2. Every extreme support plane `α` contains `n - 1` linearly independent extreme edges. -/
theorem solution {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    (∀ a' ∈ sPrimeSet S, ∃ T : Finset (Fin n → ℝ), T.card = n - 1 ∧
        (∀ ξ ∈ T, Shared.IsSupport S ξ) ∧
        LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ ξ ∈ T, ξ ⬝ᵥ a' = 0) ∧
      (∀ α : Fin n → ℝ, Shared.IsExtremeSupport S α → ∃ T : Finset (Fin n → ℝ),
        T.card = n - 1 ∧ (↑T : Set (Fin n → ℝ)) ⊆ sPrimeSet S ∧
        LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a' ∈ T, α ⬝ᵥ a' = 0) := by
          classical
          let B : LinearMap.BilinForm ℝ (Fin n → ℝ) := dotProductBilin ℝ ℝ
          have hB : B.Nondegenerate := by
            constructor <;> intro x hx <;> exact dotProduct_self_eq_zero.mp (hx x)
          have horth (W : Submodule ℝ (Fin n → ℝ)) :
              Module.finrank ℝ (B.orthogonal W) = n - Module.finrank ℝ W := by
            simpa using LinearMap.BilinForm.finrank_orthogonal hB W
          have hmem (D : Set (Fin n → ℝ)) (x : (Fin n → ℝ)) : x ∈ B.orthogonal (Submodule.span ℝ D) ↔
              ∀ a ∈ D, a ⬝ᵥ x = 0 := by
            change (∀ a ∈ Submodule.span ℝ D, a ⬝ᵥ x = 0) ↔ _
            constructor
            · exact fun h a ha => h a (Submodule.subset_span ha)
            · intro h a ha
              exact (Submodule.span_le (p := LinearMap.ker (B.flip x))).mpr h ha
          have hextract (D : Set (Fin n → ℝ)) (k : ℕ) (hk : k ≤ Module.finrank ℝ (Submodule.span ℝ D)) :
              ∃ T : Finset (Fin n → ℝ), (↑T : Set (Fin n → ℝ)) ⊆ D ∧ T.card = k ∧
                LinearIndependent ℝ (fun t : T => (t : (Fin n → ℝ))) := by
            obtain ⟨d, hd, hspan, hli⟩ := exists_linearIndependent ℝ D
            have hdf : d.Finite := hli.set_finite_of_isNoetherian
            let _ := hdf.fintype
            have hcard : k ≤ hdf.toFinset.card := by
              rw [← hspan] at hk
              have heq := finrank_span_eq_card hli
              rw [Subtype.range_coe] at heq
              rw [heq] at hk
              have heq' : hdf.toFinset = d.toFinset := by ext; simp
              rw [heq', Set.toFinset_card]
              exact hk
            obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
            have hTd : (↑T : Set (Fin n → ℝ)) ⊆ d := fun x hx => hdf.mem_toFinset.mp (hT hx)
            exact ⟨T, hTd.trans hd, hTc, hli.comp (fun t : T => (⟨t, hTd t.property⟩ : d))
              (fun x y h => Subtype.ext (show (x : (Fin n → ℝ)) = y from congrArg (fun z : d => (z : (Fin n → ℝ))) h))⟩
          have hperturb (A : Finset (Fin n → ℝ)) (x y : (Fin n → ℝ))
              (hx : ∀ a ∈ A, 0 ≤ a ⬝ᵥ x)
              (hy : ∀ a ∈ A, a ⬝ᵥ x = 0 → a ⬝ᵥ y = 0) :
              ∃ ε : ℝ, 0 < ε ∧ (∀ a ∈ A, 0 ≤ a ⬝ᵥ (x + ε • y)) ∧
                (∀ a ∈ A, 0 ≤ a ⬝ᵥ (x - ε • y)) := by
            have hn : ∀ᶠ t : ℝ in nhds 0, ∀ a ∈ A,
                a ⬝ᵥ x ≠ 0 → 0 < a ⬝ᵥ (x + t • y) := by
              rw [Filter.eventually_all_finset]
              intro a ha
              by_cases hz : a ⬝ᵥ x = 0
              · exact Filter.Eventually.of_forall (fun t h => (h hz).elim)
              · have hc : Continuous (fun t : ℝ => a ⬝ᵥ (x + t • y)) :=
                  (B a).continuous_of_finiteDimensional.comp
                    (continuous_const.add (continuous_id.smul continuous_const))
                have hp : 0 < a ⬝ᵥ (x + (0 : ℝ) • y) := by
                  simpa using lt_of_le_of_ne (hx a ha) (Ne.symm hz)
                filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hp)] with t ht using fun _ => ht
            obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hn
            have hp : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
              simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
              linarith
            have hm : -(δ / 2) ∈ Metric.ball (0 : ℝ) δ := by
              simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg] using hp
            refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
            · intro a ha
              by_cases hz : a ⬝ᵥ x = 0
              · simp [dotProduct_add, dotProduct_smul, hz, hy a ha hz]
              · exact (hd hp a ha hz).le
            · intro a ha
              by_cases hz : a ⬝ᵥ x = 0
              · simp [dotProduct_sub, dotProduct_smul, hz, hy a ha hz]
              · simpa [sub_eq_add_neg, neg_smul] using (hd hm a ha hz).le
          have hface (A : Finset (Fin n → ℝ)) (hA : Shared.NonDegenerate A) (β : (Fin n → ℝ))
              (hβ : ∀ x : (Fin n → ℝ), (∀ a ∈ A, 0 ≤ a ⬝ᵥ x) → 0 ≤ β ⬝ᵥ x) :
              ∀ x : (Fin n → ℝ), (∀ a ∈ A, 0 ≤ a ⬝ᵥ x) → β ⬝ᵥ x = 0 →
                x ∈ Submodule.span ℝ {e : (Fin n → ℝ) | IsExtremeSolution A e ∧ β ⬝ᵥ e = 0} := by
            let f : (Fin n → ℝ) →ₗ[ℝ] (A → ℝ) := LinearMap.pi (fun a : A => B a)
            let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ a : A, B a
            have hf : Function.Injective f := by
              apply (LinearMap.ker_eq_bot).mp
              apply (Submodule.eq_bot_iff _).mpr
              intro x hx
              apply hA x
              intro a ha
              have := congrFun hx (⟨a, ha⟩ : A)
              simpa [f, B, dotProduct_comm] using this
            have hl (x : (Fin n → ℝ)) : l x = ∑ a : A, (a : (Fin n → ℝ)) ⬝ᵥ x := by simp [l, B]
            have hlpos (x : (Fin n → ℝ)) (hx : ∀ a ∈ A, 0 ≤ a ⬝ᵥ x) (hx0 : x ≠ 0) : 0 < l x := by
              rw [hl]
              apply lt_of_le_of_ne (Finset.sum_nonneg (fun (a : A) _ => hx a a.property))
              intro hz
              apply hx0
              apply hA x
              intro a ha
              have hz' : ∀ a : A, (a : (Fin n → ℝ)) ⬝ᵥ x = 0 :=
                fun a => (Finset.sum_eq_zero_iff_of_nonneg (fun (a : A) _ => hx a a.property)).mp hz.symm a (Finset.mem_univ a)
              simpa [dotProduct_comm] using hz' ⟨a, ha⟩
            let K : Set (Fin n → ℝ) := f ⁻¹' Set.Icc 0 1 ∩ {x | l x = 1} ∩ {x | β ⬝ᵥ x = 0}
            have hKcomp : IsCompact K := by
              exact (((f.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hf)).isCompact_preimage isCompact_Icc).inter_right
                (isClosed_eq l.continuous_of_finiteDimensional continuous_const)).inter_right
                (isClosed_eq (B β).continuous_of_finiteDimensional continuous_const)
            have hKconv : Convex ℝ K := by
              exact (((convex_Icc (0 : A → ℝ) 1).linear_preimage f).inter
                ((convex_singleton (1 : ℝ)).linear_preimage l)).inter
                ((convex_singleton (0 : ℝ)).linear_preimage (B β))
            have hKm (x : (Fin n → ℝ)) : x ∈ K ↔
                (∀ a ∈ A, 0 ≤ a ⬝ᵥ x) ∧ l x = 1 ∧ β ⬝ᵥ x = 0 := by
              constructor
              · rintro ⟨⟨h, hlx⟩, hβx⟩
                exact ⟨fun a ha => h.1 ⟨a, ha⟩, hlx, hβx⟩
              · rintro ⟨hx, hlx, hβx⟩
                refine ⟨⟨⟨fun a => hx a a.property, fun a => ?_⟩, hlx⟩, hβx⟩
                change (a : (Fin n → ℝ)) ⬝ᵥ x ≤ 1
                rw [← hlx, hl]
                exact Finset.single_le_sum (fun (a : A) _ => hx a a.property) (Finset.mem_univ a)
            have hext (x : (Fin n → ℝ)) (hx : x ∈ K.extremePoints ℝ) : IsExtremeSolution A x := by
              obtain ⟨hsol, hlx, hβx⟩ := (hKm x).mp hx.1
              have hx0 : x ≠ 0 := by intro h; simp [h] at hlx
              let D : Set (Fin n → ℝ) := {a | a ∈ A ∧ a ⬝ᵥ x = 0}
              have hrank : n - 1 ≤ Module.finrank ℝ (Submodule.span ℝ D) := by
                by_contra hrank
                have hdim : 1 < Module.finrank ℝ (B.orthogonal (Submodule.span ℝ D)) := by
                  rw [horth]
                  omega
                have hnle : ¬ B.orthogonal (Submodule.span ℝ D) ≤ Submodule.span ℝ {x} := by
                  intro h
                  have hd := Submodule.finrank_mono h
                  rw [finrank_span_singleton hx0] at hd
                  omega
                obtain ⟨z, hz, hzx⟩ := SetLike.not_le_iff_exists.mp hnle
                let y : (Fin n → ℝ) := z - l z • x
                have hy0 : y ≠ 0 := by
                  intro h
                  apply hzx
                  exact Submodule.mem_span_singleton.mpr ⟨l z, (sub_eq_zero.mp h).symm⟩
                have hly : l y = 0 := by simp [y, hlx]
                have hdy : ∀ a ∈ A, a ⬝ᵥ x = 0 → a ⬝ᵥ y = 0 := by
                  intro a ha hax
                  have haz := (hmem D z).mp hz a ⟨ha, hax⟩
                  simp [y, dotProduct_sub, dotProduct_smul, hax, haz]
                obtain ⟨ε, hε, hp, hm⟩ := hperturb A x y hsol hdy
                have hβp := hβ (x + ε • y) hp
                have hβm := hβ (x - ε • y) hm
                have hβy : β ⬝ᵥ y = 0 := by
                  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hβx] at hβp hβm
                  nlinarith
                have hkp : x + ε • y ∈ K := (hKm _).mpr ⟨hp, by simp [hlx, hly], by simp [dotProduct_add, dotProduct_smul, hβx, hβy]⟩
                have hkm : x - ε • y ∈ K := (hKm _).mpr ⟨hm, by simp [hlx, hly], by simp [dotProduct_sub, dotProduct_smul, hβx, hβy]⟩
                have hseg : x ∈ openSegment ℝ (x + ε • y) (x - ε • y) := by
                  rw [openSegment_eq_image]
                  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
                  module
                have heq := hx.2 hkp hkm hseg
                have : ε • y = 0 := add_left_cancel (heq.trans (add_zero x).symm)
                exact hy0 ((smul_eq_zero.mp this).resolve_left hε.ne')
              obtain ⟨T, hTD, hTc, hli⟩ := hextract D (n - 1) hrank
              exact ⟨hsol, hx0, T, fun a ha => (hTD ha).1, hTc, hli, fun a ha => (hTD ha).2⟩
            let W := Submodule.span ℝ {e : (Fin n → ℝ) | IsExtremeSolution A e ∧ β ⬝ᵥ e = 0}
            have hKW : K ⊆ W := by
              rw [← closure_convexHull_extremePoints hKcomp hKconv]
              apply closure_minimal
              · apply convexHull_min _ W.convex
                intro x hx
                exact Submodule.subset_span ⟨hext x hx, ((hKm x).mp hx.1).2.2⟩
              · exact W.closed_of_finiteDimensional
            intro x hx hβx
            by_cases hx0 : x = 0
            · subst x
              exact W.zero_mem
            have hpos := hlpos x hx hx0
            have hnorm : (l x)⁻¹ • x ∈ K := by
              apply (hKm _).mpr
              refine ⟨fun a ha => ?_, ?_, ?_⟩
              · simpa [dotProduct_smul] using mul_nonneg (inv_nonneg.mpr hpos.le) (hx a ha)
              · simp [hpos.ne']
              · simp [dotProduct_smul, hβx]
            have hm := W.smul_mem (l x) (hKW hnorm)
            simpa [smul_smul, hpos.ne'] using hm
          have hfinite : ∃ E : Finset (Fin n → ℝ),
              (∀ e ∈ E, IsExtremeSolution S e) ∧
              (∀ x, IsExtremeSolution S x → ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧ x = c • e) := by
            let P := S.powerset.filter (fun (T : Finset (Fin n → ℝ)) => T.card = n - 1 ∧
              LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧
              ∃ e, IsExtremeSolution S e ∧ ∀ a ∈ T, a ⬝ᵥ e = 0)
            have hp (T : P) : ∃ e, IsExtremeSolution S e ∧ ∀ a ∈ (T : Finset (Fin n → ℝ)), a ⬝ᵥ e = 0 :=
              (Finset.mem_filter.mp T.property).2.2.2
            choose e he using hp
            refine ⟨Finset.univ.image e, ?_, ?_⟩
            · intro y hy
              obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
              exact (he t).1
            · intro x hx
              obtain ⟨T, hTS, hTc, hli, hTx⟩ := hx.2.2
              have hTP : T ∈ P := Finset.mem_filter.mpr
                ⟨Finset.mem_powerset.mpr hTS, hTc, hli, x, hx, hTx⟩
              let t : P := ⟨T, hTP⟩
              have he0 := (he t).1.2.1
              have hdim : Module.finrank ℝ (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) = n - 1 := by
                have hd := finrank_span_eq_card hli
                have hrange : Set.range (fun t : T => (t : Fin n → ℝ)) = (↑T : Set (Fin n → ℝ)) := by ext; simp
                rw [hrange, Fintype.card_coe, hTc] at hd
                exact hd
              have hyorth : e t ∈ B.orthogonal (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) :=
                (hmem _ _).mpr (he t).2
              have hsle : Submodule.span ℝ {e t} ≤ B.orthogonal (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) :=
                (Submodule.span_singleton_le_iff_mem _ _).mpr hyorth
              have heq := Submodule.eq_of_le_of_finrank_le hsle (by
                rw [horth, hdim, finrank_span_singleton he0]
                omega)
              have hxmem : x ∈ Submodule.span ℝ {e t} := by
                rw [heq]
                exact (hmem _ _).mpr hTx
              obtain ⟨c, hcx⟩ := Submodule.mem_span_singleton.mp hxmem
              have hc0 : c ≠ 0 := by intro hc; exact hx.2.1 (by simpa [hc] using hcx.symm)
              have hap : ∃ a ∈ S, 0 < a ⬝ᵥ e t := by
                by_contra! hn
                apply he0
                apply hS
                intro a ha
                have hz := le_antisymm (hn a ha) ((he t).1.1 a ha)
                simpa [dotProduct_comm] using hz
              obtain ⟨a, ha, hapos⟩ := hap
              have hcpos : 0 < c := by
                have hax := hx.1 a ha
                rw [← hcx, dotProduct_smul, smul_eq_mul] at hax
                exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right hapos).mp hax) (Ne.symm hc0)
              exact ⟨e t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, c, hcpos, hcx.symm⟩
          obtain ⟨E, hE, hrep⟩ := hfinite
          have hregion (x : Fin n → ℝ) :
              (∀ e ∈ E, 0 ≤ e ⬝ᵥ x) ↔ x ∈ regionOf (sigmaSet S) := by
            constructor
            · intro hx e he
              obtain ⟨d, hd, c, hc, rfl⟩ := hrep e he
              simpa [smul_dotProduct] using mul_nonneg hc.le (hx d hd)
            · intro hx e he
              exact hx e (hE e he)
          have hEnondeg : Shared.NonDegenerate E := by
            intro x hx
            have hzsigma : ∀ e, IsExtremeSolution S e → x ⬝ᵥ e = 0 := by
              intro e he
              obtain ⟨d, hd, c, hc, rfl⟩ := hrep e he
              simp [dotProduct_smul, hx d hd]
            have hzsol : ∀ ξ, (∀ a ∈ S, 0 ≤ a ⬝ᵥ ξ) → x ⬝ᵥ ξ = 0 := by
              intro ξ hξ
              have hm := hface S hS 0 (fun y hy => by simp) ξ hξ (by simp)
              have hs : Submodule.span ℝ {e : Fin n → ℝ | IsExtremeSolution S e ∧ (0 : Fin n → ℝ) ⬝ᵥ e = 0}
                  ≤ LinearMap.ker (B x) := by
                apply Submodule.span_le.mpr
                intro e he
                exact hzsigma e he.1
              exact hs hm
            obtain ⟨ξ₀, hξ₀⟩ := hint
            obtain ⟨ε, hε, hp, hm⟩ := hperturb S ξ₀ x (fun a ha => (hξ₀ a ha).le)
              (fun a ha hz => (ne_of_gt (hξ₀ a ha) hz).elim)
            have h0 := hzsol ξ₀ (fun a ha => (hξ₀ a ha).le)
            have h1 := hzsol (ξ₀ + ε • x) hp
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul, h0, zero_add] at h1
            exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hε.ne')
          constructor
          · intro a' ha'
            obtain ⟨_, _, T, hT, hc, hli, hz⟩ := ha'
            refine ⟨T, hc, ?_, hli, hz⟩
            intro ξ hξ
            have h := hT hξ
            exact ⟨h.2.1, fun s hs => by simpa [dotProduct_comm] using h.1 s hs⟩
          · intro α hα
            have hασ : α ∈ sigmaSet S := by
              obtain ⟨hs, T, hTS, hTc, hli, hz⟩ := hα
              exact ⟨(fun a ha => by simpa [dotProduct_comm] using hs.2 a ha), hs.1,
                T, hTS, hTc, hli, fun a ha => by simpa [dotProduct_comm] using hz a ha⟩
            let D : Set (Fin n → ℝ) := {e | e ∈ sPrimeSet S ∧ α ⬝ᵥ e = 0}
            have hsp (a : Fin n → ℝ) (ha : a ∈ S) (hαa : α ⬝ᵥ a = 0) :
                a ∈ Submodule.span ℝ D := by
              have hsol : ∀ e ∈ E, 0 ≤ e ⬝ᵥ a := by
                intro e he
                simpa [dotProduct_comm] using (hE e he).1 a ha
              have hm := hface E hEnondeg α (fun x hx => (hregion x).mp hx α hασ) a hsol hαa
              apply Submodule.span_mono _ hm
              intro e he
              refine ⟨?_, he.2⟩
              obtain ⟨hsol, he0, T, hTE, hTc, hli, hz⟩ := he.1
              exact ⟨(hregion e).mp hsol, he0, T, (fun d hd => hE d (hTE hd)), hTc, hli, hz⟩
            obtain ⟨hs, T, hTS, hTc, hli, hz⟩ := hα
            have hle : Submodule.span ℝ (↑T : Set (Fin n → ℝ)) ≤ Submodule.span ℝ D := by
              apply Submodule.span_le.mpr
              intro a ha
              exact hsp a (hTS ha) (hz a ha)
            have hdim : Module.finrank ℝ (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) = n - 1 := by
              have hd := finrank_span_eq_card hli
              have hrange : Set.range (fun t : T => (t : Fin n → ℝ)) = (↑T : Set (Fin n → ℝ)) := by ext; simp
              rw [hrange, Fintype.card_coe, hTc] at hd
              exact hd
            have hrank : n - 1 ≤ Module.finrank ℝ (Submodule.span ℝ D) := by
              rw [← hdim]
              exact Submodule.finrank_mono hle
            obtain ⟨U, hUD, hUc, hUli⟩ := hextract D (n - 1) hrank
            exact ⟨U, hUc, fun a ha => (hUD ha).1, hUli, fun a ha => (hUD ha).2⟩
