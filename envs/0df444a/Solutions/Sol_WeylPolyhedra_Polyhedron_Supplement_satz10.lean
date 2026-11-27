-- Prove2me | solution 1 for WeylPolyhedra.Polyhedron.Supplement.satz10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:18.898954+00:00
-- url     : https://prove2.me/submissions/d0d8faa6-4bb5-4ad1-a7d9-2ea224c1bee7

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_DualSystems

open WeylPolyhedra
open WeylPolyhedra.Polyhedron
open WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 IV, p. 300, Satz 10, under the hypotheses of Satz 9 kept for the rest of §3
(`S` non-degenerate, `(S)` with an inner point `ξ⁰`). Let `a′, b′, ⋯` be the extreme solutions
of the dual system `Σ` (`sPrimeSet S`). Then
1. the region `(S′)` defined by the inequalities `a′ ⬝ᵥ ξ ≥ 0` equals `(S)`, and
2. the points `a′, b′, ⋯` are a selection among the points of `S`, up to a positive factor
   (as the proof says, "bis auf einen positiven Proportionalitätsfaktor"). -/
theorem solution {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    regionOf (sPrimeSet S) = solutionRegion S ∧
      ∀ a' ∈ sPrimeSet S, ∃ a ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ a' = ρ • a := by
        classical
        obtain ⟨ξ₀, hξ₀⟩ := hint
        have K : ∀ S : Finset (Fin n → ℝ), Shared.NonDegenerate S →
            ∀ p ∈ solutionRegion S, ∀ x ∈ dualRegion S, 0 ≤ x ⬝ᵥ p := by
          intro S hS
          have key : ∀ k : ℕ, ∀ p : Fin n → ℝ, p ∈ solutionRegion S →
              (S.filter (fun a => a ⬝ᵥ p ≠ 0)).card = k → ∀ x ∈ dualRegion S, 0 ≤ x ⬝ᵥ p := by
            intro k
            induction k using Nat.strong_induction_on with
            | _ k ih =>
            intro p hp hk x hx
            by_cases hp0 : p = 0
            · simp [hp0]
            obtain ⟨b, hbS, hb⟩ : ∃ b ∈ S, b ⬝ᵥ p ≠ 0 := by
              by_contra hcon
              push Not at hcon
              exact hp0 (hS p (fun s hs => by rw [dotProduct_comm]; exact hcon s hs))
            by_cases hv : ∃ v : Fin n → ℝ, v ≠ 0 ∧ b ⬝ᵥ v = 0 ∧ ∀ a ∈ S, a ⬝ᵥ p = 0 → a ⬝ᵥ v = 0
            · obtain ⟨v, hv0, hbv, hTv⟩ := hv
              have step : ∀ w : Fin n → ℝ, b ⬝ᵥ w = 0 → (∀ a ∈ S, a ⬝ᵥ p = 0 → a ⬝ᵥ w = 0) →
                  ∃ c : ℝ, 0 ≤ c ∧ (c • p + w) ∈ solutionRegion S ∧ 0 ≤ x ⬝ᵥ (c • p + w) := by
                intro w hbw hTw
                have hne : (S.filter (fun a => a ⬝ᵥ p ≠ 0)).Nonempty :=
                  ⟨b, Finset.mem_filter.2 ⟨hbS, hb⟩⟩
                obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (S.filter (fun a => a ⬝ᵥ p ≠ 0))
                  (fun a => -(a ⬝ᵥ w) / (a ⬝ᵥ p)) hne
                have hm' := Finset.mem_filter.1 hm
                have hc : 0 ≤ -(m ⬝ᵥ w) / (m ⬝ᵥ p) := by
                  have := hmax b (Finset.mem_filter.2 ⟨hbS, hb⟩)
                  simpa [hbw] using this
                have hreg : ((-(m ⬝ᵥ w) / (m ⬝ᵥ p)) • p + w) ∈ solutionRegion S := by
                  intro a ha
                  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
                  by_cases hap : a ⬝ᵥ p = 0
                  · simp [hap, hTw a ha hap]
                  · have hpos : 0 < a ⬝ᵥ p := lt_of_le_of_ne (hp a ha) (Ne.symm hap)
                    have h1 := hmax a (Finset.mem_filter.2 ⟨ha, hap⟩)
                    have h2 := (div_le_iff₀ hpos).1 h1
                    linarith
                refine ⟨_, hc, hreg, ?_⟩
                refine ih _ ?_ _ hreg rfl x hx
                rw [← hk]
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset]
                · refine ⟨m, hm, ?_⟩
                  intro h
                  apply (Finset.mem_filter.1 h).2
                  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hm'.2]
                  ring
                · intro a ha
                  have ha' := Finset.mem_filter.1 ha
                  refine Finset.mem_filter.2 ⟨ha'.1, fun hap => ha'.2 ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hap, hTw a ha'.1 hap]
                  simp
              obtain ⟨c, hc, hcr, hcx⟩ := step v hbv hTv
              obtain ⟨d, hd, hdr, hdx⟩ := step (-v) (by simp [hbv])
                (fun a ha hap => by simp [hTv a ha hap])
              rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hcx hdx
              rw [dotProduct_neg] at hdx
              have hsum : 0 ≤ (c + d) * (x ⬝ᵥ p) := by linarith
              rcases (add_nonneg hc hd).lt_or_eq with hpos | hzero
              · exact nonneg_of_mul_nonneg_right hsum hpos
              · exfalso
                have hc0 : c = 0 := by linarith
                have hd0 : d = 0 := by linarith
                subst hc0 hd0
                apply hv0
                apply hS
                intro s hs
                have h1 := hcr s hs
                have h2 := hdr s hs
                simp at h1 h2
                rw [dotProduct_comm]
                linarith
            · -- `p` is extreme
              have hext : IsExtremeSolution S p := by
                refine ⟨hp, hp0, ?_⟩
                obtain ⟨B, hBT, hBspan, hBli⟩ := exists_linearIndependent ℝ
                  ((S.filter (fun a => a ⬝ᵥ p = 0) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
                have hBfin : B.Finite := (Finset.finite_toSet _).subset hBT
                have htop : Submodule.span ℝ (insert b B) = ⊤ := by
                  by_contra hne
                  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
                  have hfd : ∀ y : Fin n → ℝ, f y = y ⬝ᵥ (fun i => f (Pi.single i 1)) := by
                    intro y
                    conv_lhs => rw [← Finset.univ_sum_single y]
                    rw [map_sum]
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    have : (Pi.single i (y i) : Fin n → ℝ) = y i • Pi.single i 1 := by
                      rw [← Pi.single_smul]; simp
                    rw [this, map_smul, smul_eq_mul]
                  apply hv
                  refine ⟨fun i => f (Pi.single i 1), ?_, ?_, ?_⟩
                  · intro h0
                    apply hf0
                    refine LinearMap.ext (fun y => ?_)
                    rw [hfd y, h0, dotProduct_zero, LinearMap.zero_apply]
                  · rw [← hfd]
                    exact hf (Submodule.subset_span (Set.mem_insert _ _))
                  · intro a ha hap
                    rw [← hfd]
                    have hmem : a ∈ Submodule.span ℝ B := by
                      rw [hBspan]
                      exact Submodule.subset_span (by simp [ha, hap])
                    exact hf (Submodule.span_mono (Set.subset_insert _ _) hmem)
                have hcard : n - 1 ≤ hBfin.toFinset.card := by
                  have h1 := finrank_span_finset_le_card (R := ℝ) (insert b hBfin.toFinset)
                  have h2 : ((insert b hBfin.toFinset : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
                      = insert b B := by simp
                  rw [Set.finrank, h2, htop, finrank_top, Module.finrank_fin_fun] at h1
                  have h3 := Finset.card_insert_le b hBfin.toFinset
                  omega
                obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hcard
                have hTB' : ∀ t ∈ T, t ∈ B := fun t ht => by simpa using hTB ht
                have hT : ∀ t ∈ T, t ∈ S ∧ t ⬝ᵥ p = 0 := fun t ht => by
                  simpa using hBT (hTB' t ht)
                refine ⟨T, fun t ht => (hT t ht).1, hTc, ?_, fun a ha => (hT a ha).2⟩
                exact hBli.comp (fun t : T => (⟨t.1, hTB' t.1 t.2⟩ : B))
                  (fun s t hst => Subtype.ext (by simpa using hst))
              rw [dotProduct_comm]
              exact hx p hext
          intro p hp x hx
          exact key _ p hp rfl x hx
        have E : ∀ β : Fin n → ℝ, (∀ a ∈ S, 0 < a ⬝ᵥ β) → ∀ v : Fin n → ℝ,
            ∃ t : ℝ, 0 < t ∧ β - t • v ∈ solutionRegion S := by
          intro β hβ v
          have h1 : ∀ a ∈ S, ∀ᶠ t in nhds (0:ℝ), 0 < a ⬝ᵥ (β - t • v) := by
            intro a ha
            have h : Filter.Tendsto (fun t : ℝ => a ⬝ᵥ β - t * (a ⬝ᵥ v)) (nhds 0)
                (nhds (a ⬝ᵥ β - 0 * (a ⬝ᵥ v))) :=
              tendsto_const_nhds.sub (Filter.tendsto_id.mul tendsto_const_nhds)
            rw [zero_mul, sub_zero] at h
            filter_upwards [h.eventually_const_lt (hβ a ha)] with t ht
            rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
            exact ht
          have h2 := (Filter.eventually_all_finset S).2 h1
          obtain ⟨t, ht, htpos⟩ := ((h2.filter_mono nhdsWithin_le_nhds).and
            (self_mem_nhdsWithin : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0)).exists
          exact ⟨t, htpos, fun a ha => (ht a ha).le⟩
        have orth : ∀ T : Finset (Fin n → ℝ), ∀ w : Fin n → ℝ, (∀ t ∈ T, t ⬝ᵥ w = 0) →
            ∀ y ∈ Submodule.span ℝ (T : Set (Fin n → ℝ)), y ⬝ᵥ w = 0 := by
          intro T w hw y hy
          induction hy using Submodule.span_induction with
          | mem x hx => exact hw x hx
          | zero => simp
          | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
          | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]
        have L1 : ∀ T : Finset (Fin n → ℝ), LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) →
            T.card = n - 1 → ∀ u v : Fin n → ℝ, u ≠ 0 → (∀ t ∈ T, t ⬝ᵥ u = 0) →
            (∀ t ∈ T, t ⬝ᵥ v = 0) → ∃ c : ℝ, v = c • u := by
          intro T hli hcard u v hu0 hTu hTv
          have hn : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with h | h
            · subst h; exact absurd (Subsingleton.elim u 0) hu0
            · exact h
          have hus : u ∉ Submodule.span ℝ (T : Set (Fin n → ℝ)) := by
            intro h
            exact hu0 (dotProduct_self_eq_zero.1 (orth T u hTu u h))
          have huT : u ∉ T := fun h => hus (Submodule.subset_span h)
          have hli' : LinearIndepOn ℝ id ((insert u T : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            rw [Finset.coe_insert, linearIndepOn_id_insert (by simpa using huT)]
            exact ⟨hli, hus⟩
          have hfr := finrank_span_finset_eq_card hli'
          rw [Finset.card_insert_of_notMem huT, hcard, Nat.sub_add_cancel hn] at hfr
          have htop : Submodule.span ℝ ((insert u T : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) = ⊤ :=
            Submodule.eq_top_of_finrank_eq (by rw [hfr, Module.finrank_fin_fun])
          have hv : v ∈ Submodule.span ℝ ((insert u T : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            rw [htop]; exact Submodule.mem_top
          rw [Finset.coe_insert, Submodule.mem_span_insert] at hv
          obtain ⟨c, z, hz, hvz⟩ := hv
          refine ⟨c, ?_⟩
          have hzo : ∀ t ∈ T, t ⬝ᵥ z = 0 := by
            intro t ht
            have : z = v - c • u := by rw [hvz]; abel
            rw [this, dotProduct_sub, dotProduct_smul, hTu t ht, hTv t ht]; simp
          have hz0 : z = 0 := dotProduct_self_eq_zero.1 (orth T z hzo z hz)
          rw [hvz, hz0, add_zero]
        have hξ₀S : ξ₀ ∈ solutionRegion S := fun a ha => (hξ₀ a ha).le
        have hC2 : ∀ a' ∈ sPrimeSet S, ∃ a ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ a' = ρ • a := by
          intro a' ha'
          obtain ⟨hreg, hne, T, hTsub, hTcard, hTli, hTo⟩ := ha'
          have hreg' : a' ∈ dualRegion S := fun α hα => hreg α hα
          have hpos : ∀ q ∈ solutionRegion S, 0 ≤ a' ⬝ᵥ q := fun q hq => K S hS q hq a' hreg'
          have hText : ∀ α ∈ T, IsExtremeSolution S α := fun α hα => hTsub hα
          obtain ⟨a, haS, haT⟩ : ∃ a ∈ S, ∀ α ∈ T, α ⬝ᵥ a = 0 := by
            by_contra hcon
            push Not at hcon
            have hβ : ∀ a ∈ S, 0 < a ⬝ᵥ (∑ α ∈ T, α) := by
              intro a ha
              obtain ⟨α, hα, hne⟩ := hcon a ha
              rw [dotProduct_sum]
              apply Finset.sum_pos' (fun i hi => (hText i hi).1 a ha) ⟨α, hα, ?_⟩
              exact lt_of_le_of_ne ((hText α hα).1 a ha) (by rw [dotProduct_comm]; exact Ne.symm hne)
            have hβ0 : a' ⬝ᵥ (∑ α ∈ T, α) = 0 := by
              rw [dotProduct_sum]
              exact Finset.sum_eq_zero (fun α hα => by rw [dotProduct_comm]; exact hTo α hα)
            obtain ⟨t, ht, hmem⟩ := E _ hβ a'
            have h := hpos _ hmem
            rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hβ0] at h
            have hpp : 0 < a' ⬝ᵥ a' := by
              rcases (show (0:ℝ) ≤ a' ⬝ᵥ a' from
                Finset.sum_nonneg (fun i _ => mul_self_nonneg (a' i))).lt_or_eq with h' | h'
              · exact h'
              · exact absurd (dotProduct_self_eq_zero.1 h'.symm) hne
            nlinarith
          obtain ⟨c, hc⟩ := L1 T hTli hTcard a' a hne hTo haT
          have h1 := hξ₀ a haS
          have h2 := hpos ξ₀ hξ₀S
          rw [hc, smul_dotProduct, smul_eq_mul] at h1
          have hcpos : 0 < c := by
            by_contra hcn
            push Not at hcn
            nlinarith
          refine ⟨a, haS, c⁻¹, inv_pos.2 hcpos, ?_⟩
          rw [hc, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
        refine ⟨?_, hC2⟩
        have hscale : ∀ α : Fin n → ℝ, IsExtremeSolution S α → ∀ c : ℝ, 0 < c →
            IsExtremeSolution S (c • α) := by
          intro α hα c hc
          obtain ⟨hreg, hne, T, hTS, hTc, hTli, hTo⟩ := hα
          refine ⟨fun a ha => ?_, smul_ne_zero hc.ne' hne, T, hTS, hTc, hTli, fun a ha => ?_⟩
          · rw [dotProduct_smul, smul_eq_mul]; exact mul_nonneg hc.le (hreg a ha)
          · rw [dotProduct_smul, hTo a ha, smul_zero]
        have hnorm : ∀ α : Fin n → ℝ, IsExtremeSolution S α → 0 < (∑ a ∈ S, a) ⬝ᵥ α := by
          intro α hα
          rw [sum_dotProduct]
          obtain ⟨b, hbS, hb⟩ : ∃ b ∈ S, b ⬝ᵥ α ≠ 0 := by
            by_contra hcon
            push Not at hcon
            exact hα.2.1 (hS α (fun s hs => by rw [dotProduct_comm]; exact hcon s hs))
          exact Finset.sum_pos' (fun i hi => hα.1 i hi) ⟨b, hbS, lt_of_le_of_ne (hα.1 b hbS) (Ne.symm hb)⟩
        set N : Set (Fin n → ℝ) := {α | IsExtremeSolution S α ∧ (∑ a ∈ S, a) ⬝ᵥ α = 1} with hNdef
        have hNfin : N.Finite := by
          apply Set.Finite.of_finite_image (f := fun α => S.filter (fun a => a ⬝ᵥ α = 0))
          · apply (S.powerset.finite_toSet).subset
            rintro _ ⟨α, -, rfl⟩
            simp
            exact fun x hx => hx.1
          · intro α hα β hβ hfeq
            obtain ⟨⟨-, hne, T, hTS, hTc, hTli, hTo⟩, hα1⟩ := hα
            have hTβ : ∀ t ∈ T, t ⬝ᵥ β = 0 := by
              intro t ht
              have hmem : t ∈ S.filter (fun a => a ⬝ᵥ α = 0) := Finset.mem_filter.2 ⟨hTS ht, hTo t ht⟩
              have hmem' : t ∈ S.filter (fun a => a ⬝ᵥ β = 0) := by
                have := hfeq
                simp only at this
                rw [this] at hmem; exact hmem
              exact (Finset.mem_filter.1 hmem').2
            obtain ⟨c, hc⟩ := L1 T hTli hTc α β hne hTo hTβ
            have h1 := hβ.2
            rw [hc, dotProduct_smul, smul_eq_mul, hα1, mul_one] at h1
            rw [hc, h1, one_smul]
        set S₂ := hNfin.toFinset with hS₂def
        have hmem : ∀ α, α ∈ S₂ ↔ IsExtremeSolution S α ∧ (∑ a ∈ S, a) ⬝ᵥ α = 1 := by
          intro α; rw [hS₂def, Set.Finite.mem_toFinset]; exact Iff.rfl
        have hrep : ∀ α, IsExtremeSolution S α → ∃ α₀ ∈ S₂, ∃ c : ℝ, 0 < c ∧ α = c • α₀ := by
          intro α hα
          have hp := hnorm α hα
          refine ⟨((∑ a ∈ S, a) ⬝ᵥ α)⁻¹ • α, (hmem _).2 ⟨hscale α hα _ (inv_pos.2 hp), ?_⟩,
            (∑ a ∈ S, a) ⬝ᵥ α, hp, ?_⟩
          · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']
          · rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
        have hS₂nd : Shared.NonDegenerate S₂ := by
          intro p hp
          have hp' : ∀ α, IsExtremeSolution S α → α ⬝ᵥ p = 0 := by
            intro α hα
            obtain ⟨α₀, h0, c, hc, rfl⟩ := hrep α hα
            rw [smul_dotProduct, dotProduct_comm, hp α₀ h0, smul_zero]
          have hd1 : p ∈ dualRegion S := fun α hα => (hp' α hα).ge
          have hd2 : -p ∈ dualRegion S := fun α hα => by rw [dotProduct_neg, hp' α hα, neg_zero]
          have k1 := K S hS ξ₀ hξ₀S p hd1
          have k2 := K S hS ξ₀ hξ₀S (-p) hd2
          rw [neg_dotProduct] at k2
          obtain ⟨t, ht, htm⟩ := E ξ₀ hξ₀ p
          have k3 := K S hS _ htm p hd1
          rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at k3
          have hpp : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg (fun i _ => mul_self_nonneg (p i))
          have : p ⬝ᵥ p = 0 := by nlinarith
          exact dotProduct_self_eq_zero.1 this
        ext ξ
        constructor
        · intro hξ a ha
          have hx : ξ ∈ dualRegion S₂ := by
            intro a' ha'
            apply hξ a'
            obtain ⟨hreg, hne, T, hTS₂, hc, hli, ho⟩ := ha'
            refine ⟨?_, hne, T, ?_, hc, hli, ho⟩
            · intro α hα
              obtain ⟨α₀, h0, c, hc, rfl⟩ := hrep α hα
              rw [smul_dotProduct, smul_eq_mul]
              exact mul_nonneg hc.le (hreg α₀ h0)
            · intro t ht
              exact ((hmem t).1 (hTS₂ ht)).1
          have hpa : a ∈ solutionRegion S₂ := fun α hα => by
            rw [dotProduct_comm]; exact ((hmem α).1 hα).1.1 a ha
          have := K S₂ hS₂nd a hpa ξ hx
          rw [dotProduct_comm]; exact this
        · intro hξ a' ha'
          obtain ⟨a, haS, ρ, hρ, rfl⟩ := hC2 a' ha'
          rw [smul_dotProduct, smul_eq_mul]
          exact mul_nonneg hρ.le (hξ a haS)
