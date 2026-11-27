-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.Supplement.satz11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:37.336696+00:00
-- url     : https://prove2.me/submissions/dbfd2351-8ee3-43f1-af69-fb54e7b36017

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

open WeylPolyhedra
open WeylPolyhedra.Polyhedron
open WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 11, under the hypotheses of Satz 9 kept for the rest of §3
(`S` non-degenerate, `(S)` with an inner point `ξ⁰`): the systems `S′` and `Σ` are mutually
dual. `S′` consists of the extreme solutions of `Σ` by definition (`sPrimeSet S`); the content
is the converse, stated in the sentence before Satz 11: the extreme solutions of `S′` are exactly
the extreme solutions of `S`, i.e. the inequalities of `Σ`. -/
theorem solution {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ ξ : Fin n → ℝ, IsExtremeSolutionOf (sPrimeSet S) ξ ↔ IsExtremeSolution S ξ := by
      have ORTHSPAN : ∀ (B : Set (Fin n → ℝ)) (v : Fin n → ℝ), (∀ b ∈ B, b ⬝ᵥ v = 0) →
          ∀ w ∈ Submodule.span ℝ B, w ⬝ᵥ v = 0 := by
        intro B v hB w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hB x hx
        | zero => simp
        | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
        | smul a x _ hx => rw [smul_dotProduct, hx, smul_zero]
      have NOTSPAN : ∀ (B : Set (Fin n → ℝ)) (u : Fin n → ℝ), u ≠ 0 → (∀ b ∈ B, b ⬝ᵥ u = 0) →
          u ∉ Submodule.span ℝ B := by
        intro B u hu hB hmem
        exact hu (dotProduct_self_eq_zero.mp (ORTHSPAN B u hB u hmem))
      have EXTRACT : ∀ (B : Set (Fin n → ℝ)), n - 1 ≤ Module.finrank ℝ (Submodule.span ℝ B) →
          ∃ T : Finset (Fin n → ℝ), (↑T : Set (Fin n → ℝ)) ⊆ B ∧ T.card = n - 1 ∧
            LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) := by
        intro B hB
        obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent ℝ B
        have hfin : b.Finite := hli.setFinite
        set bF := hfin.toFinset with hbF
        have hcoe : (↑bF : Set (Fin n → ℝ)) = b := hfin.coe_toFinset
        have hcard : Module.finrank ℝ (Submodule.span ℝ (↑bF : Set (Fin n → ℝ))) = bF.card := by
          apply finrank_span_finset_eq_card
          rw [hcoe]; exact hli
        rw [hcoe, hspan] at hcard
        obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (s := bF) (n := n - 1) (by omega)
        refine ⟨T, ?_, hTc, ?_⟩
        · intro x hx; exact hbB (hcoe ▸ (Finset.coe_subset.mpr hT) hx)
        · have : (↑T : Set (Fin n → ℝ)) ⊆ b := hcoe ▸ Finset.coe_subset.mpr hT
          exact LinearIndepOn.mono (v := id) hli this
      have MONO : ∀ (B : Set (Fin n → ℝ)) (T : Finset (Fin n → ℝ)), T.card = n - 1 →
          LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) → (↑T : Set (Fin n → ℝ)) ⊆ Submodule.span ℝ B →
          n - 1 ≤ Module.finrank ℝ (Submodule.span ℝ B) := by
        intro B T hc hli hsub
        have h1 : Module.finrank ℝ (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) = T.card :=
          finrank_span_finset_eq_card hli
        rw [← hc, ← h1]
        exact Submodule.finrank_mono (Submodule.span_le.mpr hsub)
      have ORTH : ∀ (B : Set (Fin n → ℝ)), Module.finrank ℝ (Submodule.span ℝ B) < n →
          ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ b ∈ B, b ⬝ᵥ d = 0 := by
        intro B hB
        have hlt : Submodule.span ℝ B < ⊤ := by
          rw [lt_top_iff_ne_top]; intro h
          rw [h, finrank_top, Module.finrank_fin_fun] at hB; omega
        obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
        refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
        · intro hd; apply hf0
          apply LinearMap.ext; intro x
          rw [LinearMap.pi_apply_eq_sum_univ f x]
          simp only [LinearMap.zero_apply]
          apply Finset.sum_eq_zero; intro i _
          have := congrFun hd i
          simp only [Pi.zero_apply] at this
          have e : (fun j => if i = j then (1:ℝ) else 0) = Pi.single i 1 := by
            ext j; simp [Pi.single_apply, eq_comm]
          rw [e, this, smul_zero]
        · intro b hb
          have hfb : f b = 0 := by
            have : f b ∈ (Submodule.span ℝ B).map f := Submodule.mem_map_of_mem (Submodule.subset_span hb)
            rw [hf] at this; simpa using this
          rw [LinearMap.pi_apply_eq_sum_univ f b] at hfb
          rw [← hfb, dotProduct]
          apply Finset.sum_congr rfl; intro i _
          have e : (fun j => if i = j then (1:ℝ) else 0) = Pi.single i 1 := by
            ext j; simp [Pi.single_apply, eq_comm]
          rw [e, smul_eq_mul]
      have INS : ∀ (B : Set (Fin n → ℝ)) (c : Fin n → ℝ),
          Module.finrank ℝ (Submodule.span ℝ (insert c B)) ≤ Module.finrank ℝ (Submodule.span ℝ B) + 1 := by
        intro B c
        rw [Submodule.span_insert]
        refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
        have : Module.finrank ℝ (Submodule.span ℝ ({c} : Set (Fin n → ℝ))) ≤ 1 := by
          have := finrank_span_le_card (R := ℝ) ({c} : Set (Fin n → ℝ))
          simpa using this
        omega
      have M1 : ∀ (A : Set (Fin n → ℝ)) (F : Finset (Fin n → ℝ)), (↑F : Set (Fin n → ℝ)) ⊆ A →
          (∀ a ∈ A, ∃ f ∈ F, ∃ r : ℝ, 0 < r ∧ a = r • f) → ∀ c : Fin n → ℝ,
          (∀ y ∈ regionOf A, c ⬝ᵥ y = 0 → y = 0) → ∀ v : Fin n → ℝ,
          (∀ e, IsExtremeSolutionOf A e → 0 ≤ e ⬝ᵥ v) → ∀ x ∈ regionOf A,
          0 ≤ x ⬝ᵥ v ∧ (x ⬝ᵥ v = 0 → x ∈ Submodule.span ℝ {e | IsExtremeSolutionOf A e ∧ e ⬝ᵥ v = 0}) := by
        intro A F hFA hF c hc v hv
        classical
        let Q : (Fin n → ℝ) → Prop := fun x =>
          0 ≤ x ⬝ᵥ v ∧ (x ⬝ᵥ v = 0 → x ∈ Submodule.span ℝ {e | IsExtremeSolutionOf A e ∧ e ⬝ᵥ v = 0})
        let rk : (Fin n → ℝ) → ℕ := fun x =>
          Module.finrank ℝ (Submodule.span ℝ {a | a ∈ A ∧ a ⬝ᵥ x = 0})
        have Q0 : Q 0 := ⟨by simp, fun _ => Submodule.zero_mem _⟩
        have Qe : ∀ e, IsExtremeSolutionOf A e → Q e := fun e he =>
          ⟨hv e he, fun h => Submodule.subset_span ⟨he, h⟩⟩
        have Qc : ∀ y z : Fin n → ℝ, ∀ p q : ℝ, 0 < p → 0 < q → Q y → Q z → Q (p • y + q • z) := by
          intro y z p q hp hq hy hz
          have e1 : (p • y + q • z) ⬝ᵥ v = p * (y ⬝ᵥ v) + q * (z ⬝ᵥ v) := by
            rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
          have h1 := mul_nonneg hp.le hy.1
          have h2 := mul_nonneg hq.le hz.1
          refine ⟨by rw [e1]; linarith, fun h0 => ?_⟩
          rw [e1] at h0
          have hy0 : y ⬝ᵥ v = 0 := by
            have : p * (y ⬝ᵥ v) = 0 := by linarith
            rcases mul_eq_zero.mp this with h | h
            · linarith
            · exact h
          have hz0 : z ⬝ᵥ v = 0 := by
            have : q * (z ⬝ᵥ v) = 0 := by linarith
            rcases mul_eq_zero.mp this with h | h
            · linarith
            · exact h
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hy.2 hy0)) (Submodule.smul_mem _ _ (hz.2 hz0))
        have MOVE : ∀ x ∈ regionOf A, ∀ d : Fin n → ℝ, d ∉ regionOf A →
            (∀ a ∈ {a | a ∈ A ∧ a ⬝ᵥ x = 0}, a ⬝ᵥ d = 0) →
            ∃ t : ℝ, 0 < t ∧ x + t • d ∈ regionOf A ∧ rk x < rk (x + t • d) := by
          intro x hx d hd hperp
          set F' := F.filter (fun f => f ⬝ᵥ d < 0) with hF'
          have hne : F'.Nonempty := by
            by_contra hne; apply hd; intro a ha
            obtain ⟨f, hf, r, hr, rfl⟩ := hF a ha
            have : ¬ f ⬝ᵥ d < 0 := fun h => hne ⟨f, Finset.mem_filter.mpr ⟨hf, h⟩⟩
            rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg hr.le (not_lt.mp this)
          obtain ⟨g, hgF', hgmin⟩ := F'.exists_min_image (fun f => (f ⬝ᵥ x) / (-(f ⬝ᵥ d))) hne
          rw [Finset.mem_filter] at hgF'
          have hgA : g ∈ A := hFA (Finset.mem_coe.mpr hgF'.1)
          have hgd := hgF'.2
          have hgx : 0 ≤ g ⬝ᵥ x := hx g hgA
          have hgx' : g ⬝ᵥ x ≠ 0 := fun h => by have := hperp g ⟨hgA, h⟩; linarith
          set t := (g ⬝ᵥ x) / (-(g ⬝ᵥ d)) with ht_def
          have ht : 0 < t := div_pos (lt_of_le_of_ne hgx (Ne.symm hgx')) (by linarith)
          have hgt : g ⬝ᵥ (x + t • d) = 0 := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ht_def]
            have : g ⬝ᵥ d ≠ 0 := ne_of_lt hgd
            field_simp
            ring
          have hreg : x + t • d ∈ regionOf A := by
            intro a ha
            obtain ⟨f, hf, r, hr, rfl⟩ := hF a ha
            have hfx : 0 ≤ f ⬝ᵥ x := by
              have := hx _ ha
              rw [smul_dotProduct, smul_eq_mul] at this
              by_contra h; push Not at h; nlinarith
            rw [smul_dotProduct, smul_eq_mul, dotProduct_add, dotProduct_smul, smul_eq_mul]
            apply mul_nonneg hr.le
            by_cases hfd : f ⬝ᵥ d < 0
            · have := hgmin f (Finset.mem_filter.mpr ⟨hf, hfd⟩)
              rw [le_div_iff₀ (by linarith)] at this
              nlinarith
            · push Not at hfd; nlinarith [mul_nonneg ht.le hfd]
          refine ⟨t, ht, hreg, ?_⟩
          apply Submodule.finrank_lt_finrank_of_lt
          rw [SetLike.lt_iff_le_and_exists]
          constructor
          · apply Submodule.span_mono
            rintro a ⟨haA, hax⟩
            refine ⟨haA, ?_⟩
            rw [dotProduct_add, dotProduct_smul, hax, hperp a ⟨haA, hax⟩]; simp
          · refine ⟨g, Submodule.subset_span ⟨hgA, hgt⟩, ?_⟩
            intro hmem
            have := ORTHSPAN _ d hperp g hmem
            linarith
        have STEP : ∀ x ∈ regionOf A, x ≠ 0 → rk x < n - 1 → ∃ y z : Fin n → ℝ, ∃ p q : ℝ,
            0 < p ∧ 0 < q ∧ x = p • y + q • z ∧ y ∈ regionOf A ∧ z ∈ regionOf A ∧
            rk x < rk y ∧ rk x < rk z := by
          intro x hx _ hr
          obtain ⟨d, hd0, hd⟩ := ORTH (insert c {a | a ∈ A ∧ a ⬝ᵥ x = 0})
            (by have := INS {a | a ∈ A ∧ a ⬝ᵥ x = 0} c; simp only [rk] at hr; omega)
          have hcd : c ⬝ᵥ d = 0 := hd c (Set.mem_insert _ _)
          have hperp : ∀ a ∈ {a | a ∈ A ∧ a ⬝ᵥ x = 0}, a ⬝ᵥ d = 0 :=
            fun a ha => hd a (Set.mem_insert_of_mem _ ha)
          have hdn : d ∉ regionOf A := fun h => hd0 (hc d h hcd)
          have hdn' : -d ∉ regionOf A := fun h => hd0 (neg_eq_zero.mp (hc (-d) h (by simp [hcd])))
          obtain ⟨t₁, ht₁, hy, hry⟩ := MOVE x hx d hdn hperp
          obtain ⟨t₂, ht₂, hz, hrz⟩ := MOVE x hx (-d) hdn' (fun a ha => by simp [hperp a ha])
          refine ⟨_, _, t₂ / (t₁ + t₂), t₁ / (t₁ + t₂), by positivity, by positivity, ?_, hy, hz, hry, hrz⟩
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
          field_simp
          ring
        have KEY : ∀ k : ℕ, ∀ x ∈ regionOf A, n - rk x ≤ k → Q x := by
          intro k
          induction k with
          | zero =>
            intro x hx hk
            by_cases hx0 : x = 0
            · rw [hx0]; exact Q0
            obtain ⟨T, hT, hTc, hTli⟩ := EXTRACT {a | a ∈ A ∧ a ⬝ᵥ x = 0} (by simp only [rk] at hk; omega)
            exact Qe x ⟨hx, hx0, T, fun a ha => (hT ha).1, hTc, hTli, fun a ha => (hT ha).2⟩
          | succ k ih =>
            intro x hx hk
            by_cases hx0 : x = 0
            · rw [hx0]; exact Q0
            by_cases hr : n - 1 ≤ rk x
            · obtain ⟨T, hT, hTc, hTli⟩ := EXTRACT _ hr
              exact Qe x ⟨hx, hx0, T, fun a ha => (hT ha).1, hTc, hTli, fun a ha => (hT ha).2⟩
            push Not at hr
            obtain ⟨y, z, p, q, hp, hq, rfl, hy, hz, hry, hrz⟩ := STEP x hx hx0 hr
            exact Qc y z p q hp hq (ih y hy (by omega)) (ih z hz (by omega))
        intro x hx
        exact KEY _ x hx le_rfl
      have LINE : ∀ (T : Finset (Fin n → ℝ)), T.card = n - 1 →
          LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) → ∀ u w : Fin n → ℝ, u ≠ 0 →
          (∀ a ∈ T, a ⬝ᵥ u = 0) → (∀ a ∈ T, a ⬝ᵥ w = 0) → ∃ k : ℝ, w = k • u := by
        intro T hTc hli u w hu hTu hTw
        have huu : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
        refine ⟨(w ⬝ᵥ u) / (u ⬝ᵥ u), ?_⟩
        by_contra hne
        set γ := w - ((w ⬝ᵥ u) / (u ⬝ᵥ u)) • u with hγ
        have hγ0 : γ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
        have hu_ns : u ∉ Submodule.span ℝ (↑T : Set (Fin n → ℝ)) := NOTSPAN _ u hu hTu
        have hγperp : ∀ b ∈ insert u (↑T : Set (Fin n → ℝ)), b ⬝ᵥ γ = 0 := by
          intro b hb
          rw [Set.mem_insert_iff] at hb
          rcases hb with hb | hb
          · rw [hb, hγ, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm u w]
            field_simp
            ring
          · rw [hγ, dotProduct_sub, dotProduct_smul, smul_eq_mul, hTw b hb, hTu b hb]; ring
        have hγ_ns := NOTSPAN _ γ hγ0 hγperp
        have hli2 : LinearIndepOn ℝ id (insert γ (insert u (↑T : Set (Fin n → ℝ)))) :=
          (LinearIndepOn.id_insert hli hu_ns).id_insert hγ_ns
        have hγT : γ ∉ insert u T := fun h => hγ_ns (Submodule.subset_span (by simpa using h))
        have huT : u ∉ T := fun h => hu_ns (Submodule.subset_span h)
        have hcoe : (↑(insert γ (insert u T)) : Set (Fin n → ℝ)) =
            insert γ (insert u (↑T : Set (Fin n → ℝ))) := by push_cast; rfl
        rw [← hcoe] at hli2
        have := LinearIndependent.fintype_card_le_finrank hli2
        rw [Module.finrank_fin_fun] at this
        simp only [Finset.coe_sort_coe, Fintype.card_coe] at this
        rw [Finset.card_insert_of_notMem hγT, Finset.card_insert_of_notMem huT] at this
        omega
      have HINT : ∀ p v : Fin n → ℝ, (∀ a ∈ S, 0 < a ⬝ᵥ p) →
          ∃ t : ℝ, 0 < t ∧ ∀ a ∈ S, 0 ≤ a ⬝ᵥ (p + t • v) := by
        intro p v hp
        have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ a ∈ S, 0 < a ⬝ᵥ (p + t • v) := by
          rw [Filter.eventually_all_finset]
          intro a ha
          have hc : Filter.Tendsto (fun t : ℝ => a ⬝ᵥ p + t * (a ⬝ᵥ v)) (nhdsWithin (0:ℝ) (Set.Ioi 0))
              (nhds (a ⬝ᵥ p + 0 * (a ⬝ᵥ v))) :=
            ((tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds))).mono_left
              nhdsWithin_le_nhds
          rw [zero_mul, add_zero] at hc
          filter_upwards [hc.eventually (lt_mem_nhds (hp a ha))] with t ht
          rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; exact ht
        obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
        exact ⟨t, ht0, fun a ha => (ht a ha).le⟩
      have SELF : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ y := fun y =>
        Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
      obtain ⟨ξ₀, hξ₀⟩ := hint
      have hS0 : ∀ a ∈ S, a ≠ 0 := fun a ha h => by
        have := hξ₀ a ha; rw [h, zero_dotProduct] at this; exact lt_irrefl _ this
      have hextS : ∀ x, IsExtremeSolutionOf (↑S : Set (Fin n → ℝ)) x ↔ IsExtremeSolution S x := by
        intro x; constructor
        · rintro ⟨h1, h2, T, hT, h3, h4, h5⟩; exact ⟨h1, h2, T, Finset.coe_subset.mp hT, h3, h4, h5⟩
        · rintro ⟨h1, h2, T, hT, h3, h4, h5⟩; exact ⟨h1, h2, T, Finset.coe_subset.mpr hT, h3, h4, h5⟩
      have hcS : ∀ y ∈ regionOf (↑S : Set (Fin n → ℝ)), (∑ a ∈ S, a) ⬝ᵥ y = 0 → y = 0 := by
        intro y hy h0
        rw [sum_dotProduct] at h0
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => hy a ha)).mp h0
        apply hS; intro s hs; rw [dotProduct_comm]; exact this s hs
      have PS : ∀ v, (∀ e, IsExtremeSolution S e → 0 ≤ e ⬝ᵥ v) → ∀ x ∈ solutionRegion S,
          0 ≤ x ⬝ᵥ v := fun v hv x hx =>
        (M1 (↑S) S subset_rfl (fun a ha => ⟨a, ha, 1, one_pos, (one_smul _ _).symm⟩) _ hcS v
          (fun e he => hv e ((hextS e).mp he)) x hx).1
      have hSsub : ∀ a ∈ S, a ∈ regionOf (sigmaSet S) := by
        intro a ha α hα; rw [dotProduct_comm]; exact hα.1 a ha
      have hSigSpan : ∀ v, (∀ α ∈ sigmaSet S, α ⬝ᵥ v = 0) → v = 0 := by
        intro v hv
        obtain ⟨t, ht, hreg⟩ := HINT ξ₀ v hξ₀
        have hv1 : ∀ e, IsExtremeSolution S e → 0 ≤ e ⬝ᵥ v := fun e he => (hv e he).ge
        have hv2 : ∀ e, IsExtremeSolution S e → 0 ≤ e ⬝ᵥ (-v) := fun e he => by
          rw [dotProduct_neg, hv e he, neg_zero]
        have h1 := PS v hv1 ξ₀ (fun a ha => (hξ₀ a ha).le)
        have h2 := PS (-v) hv2 ξ₀ (fun a ha => (hξ₀ a ha).le)
        have h3 := PS v hv1 _ hreg
        have h4 := PS (-v) hv2 _ hreg
        rw [dotProduct_neg] at h2 h4
        rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h3 h4
        have : v ⬝ᵥ v = 0 := by
          have h5 : t * (v ⬝ᵥ v) = 0 := by linarith
          rcases mul_eq_zero.mp h5 with h | h
          · linarith
          · exact h
        exact dotProduct_self_eq_zero.mp this
      have hcSig : ∀ y ∈ regionOf (sigmaSet S), ξ₀ ⬝ᵥ y = 0 → y = 0 := by
        intro y hy h0
        obtain ⟨t, ht, hreg⟩ := HINT ξ₀ (-y) hξ₀
        have h3 := PS y (fun e he => hy e he) _ hreg
        rw [add_dotProduct, smul_dotProduct, smul_eq_mul, neg_dotProduct, h0] at h3
        have := SELF y
        have : y ⬝ᵥ y = 0 := by nlinarith
        exact dotProduct_self_eq_zero.mp this
      have hFin : ∃ F : Finset (Fin n → ℝ), (↑F : Set (Fin n → ℝ)) ⊆ sigmaSet S ∧
          ∀ α ∈ sigmaSet S, ∃ f ∈ F, ∃ r : ℝ, 0 < r ∧ α = r • f := by
        classical
        let pick : Finset (Fin n → ℝ) → (Fin n → ℝ) := fun T =>
          if h : ∃ β, IsExtremeSolution S β ∧ T.card = n - 1 ∧
              LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a ∈ T, a ⬝ᵥ β = 0
          then Classical.choose h else 0
        refine ⟨(S.powerset.image pick).filter (fun β => IsExtremeSolution S β), ?_, ?_⟩
        · intro β hβ
          rw [Finset.mem_coe, Finset.mem_filter] at hβ
          exact hβ.2
        · intro α hα
          obtain ⟨hαreg, hα0, T, hTS, hTc, hTli, hTα⟩ := hα
          have h : ∃ β, IsExtremeSolution S β ∧ T.card = n - 1 ∧
              LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a ∈ T, a ⬝ᵥ β = 0 :=
            ⟨α, ⟨hαreg, hα0, T, hTS, hTc, hTli, hTα⟩, hTc, hTli, hTα⟩
          have hpick : pick T = Classical.choose h := by simp only [pick, dif_pos h]
          obtain ⟨hβ, -, -, hTβ⟩ := Classical.choose_spec h
          set β := Classical.choose h
          refine ⟨β, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨T, Finset.mem_powerset.mpr hTS, hpick⟩, hβ⟩
          obtain ⟨k, hk⟩ := LINE T hTc hTli β α hβ.2.1 hTβ hTα
          refine ⟨k, ?_, hk⟩
          rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
          · exfalso; apply hβ.2.1
            apply hS; intro s hs
            have h1 := hβ.1 s hs
            have h2 := hαreg s hs
            rw [hk, dotProduct_smul, smul_eq_mul] at h2
            rw [dotProduct_comm]; nlinarith
          · exfalso; apply hα0; rw [hk, hk0, zero_smul]
          · exact hk0
      obtain ⟨F, hFsub, hFrep⟩ := hFin
      have MS' := M1 (sigmaSet S) F hFsub hFrep ξ₀ hcSig
      have POS : ∀ a' ∈ sPrimeSet S, ∃ s ∈ S, ∃ r : ℝ, 0 < r ∧ a' = r • s := by
        intro a' ha'
        obtain ⟨ha'reg, ha'0, T', hT'Sig, hT'c, hT'li, hT'perp⟩ := ha'
        have hy : ∀ s ∈ S, 0 ≤ s ⬝ᵥ (∑ α ∈ T', α) := by
          intro s hs; rw [dotProduct_sum]
          exact Finset.sum_nonneg (fun α hα => (hT'Sig hα).1 s hs)
        by_cases hcase : ∃ s ∈ S, s ⬝ᵥ (∑ α ∈ T', α) = 0
        · obtain ⟨s, hs, hs0⟩ := hcase
          rw [dotProduct_sum] at hs0
          have hsα := (Finset.sum_eq_zero_iff_of_nonneg (fun α hα => (hT'Sig hα).1 s hs)).mp hs0
          obtain ⟨k, hk⟩ := LINE T' hT'c hT'li a' s ha'0 hT'perp
            (fun α hα => by rw [dotProduct_comm]; exact hsα α hα)
          rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
          · exfalso; apply ha'0; apply hSigSpan; intro α hα
            have h1 := ha'reg α hα
            have h2 := hα.1 s hs
            rw [hk, smul_dotProduct, smul_eq_mul, dotProduct_comm a' α] at h2
            nlinarith
          · exfalso; apply hS0 s hs; rw [hk, hk0, zero_smul]
          · refine ⟨s, hs, k⁻¹, inv_pos.mpr hk0, ?_⟩
            rw [hk, smul_smul, inv_mul_cancel₀ hk0.ne', one_smul]
        · push Not at hcase
          have hpos : ∀ s ∈ S, 0 < s ⬝ᵥ (∑ α ∈ T', α) := fun s hs =>
            lt_of_le_of_ne (hy s hs) (Ne.symm (hcase s hs))
          obtain ⟨t, ht, hreg⟩ := HINT _ (-a') hpos
          have h3 := PS a' (fun e he => ha'reg e he) _ hreg
          rw [add_dotProduct, smul_dotProduct, smul_eq_mul, neg_dotProduct, sum_dotProduct,
            Finset.sum_eq_zero (fun α hα => hT'perp α hα)] at h3
          have := SELF a'
          have : a' ⬝ᵥ a' = 0 := by nlinarith
          exact absurd (dotProduct_self_eq_zero.mp this) ha'0
      intro ξ
      constructor
      · rintro ⟨hreg, h0, T', hT', hc, hli, hperp⟩
        have hv : ∀ e, IsExtremeSolutionOf (sigmaSet S) e → 0 ≤ e ⬝ᵥ ξ := fun e he => hreg e he
        refine ⟨fun a ha => (MS' ξ hv a (hSsub a ha)).1, h0, ?_⟩
        have hsub : (↑T' : Set (Fin n → ℝ)) ⊆
            Submodule.span ℝ {s | s ∈ (↑S : Set (Fin n → ℝ)) ∧ s ⬝ᵥ ξ = 0} := by
          intro a' ha'
          obtain ⟨s, hs, r, hr, rfl⟩ := POS a' (hT' ha')
          have h1 := hperp (r • s) ha'
          rw [smul_dotProduct, smul_eq_mul] at h1
          have hs0 : s ⬝ᵥ ξ = 0 := by
            rcases mul_eq_zero.mp h1 with h | h
            · linarith
            · exact h
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hs, hs0⟩)
        obtain ⟨T, hT, hTc, hTli⟩ := EXTRACT _ (MONO _ T' hc hli hsub)
        exact ⟨T, fun a ha => (hT ha).1, hTc, hTli, fun a ha => (hT ha).2⟩
      · intro hξ
        obtain ⟨hreg, h0, T, hTS, hc, hli, hperp⟩ := hξ
        have hv : ∀ e, IsExtremeSolutionOf (sigmaSet S) e → 0 ≤ e ⬝ᵥ ξ := fun e he => by
          rw [dotProduct_comm]; exact he.1 ξ ⟨hreg, h0, T, hTS, hc, hli, hperp⟩
        refine ⟨hv, h0, ?_⟩
        have hsub : (↑T : Set (Fin n → ℝ)) ⊆
            Submodule.span ℝ {e | IsExtremeSolutionOf (sigmaSet S) e ∧ e ⬝ᵥ ξ = 0} :=
          fun t ht => (MS' ξ hv t (hSsub t (hTS ht))).2 (hperp t ht)
        obtain ⟨T', hT', hT'c, hT'li⟩ := EXTRACT _ (MONO _ T hc hli hsub)
        exact ⟨T', fun a ha => (hT' ha).1, hT'c, hT'li, fun a ha => (hT' ha).2⟩
