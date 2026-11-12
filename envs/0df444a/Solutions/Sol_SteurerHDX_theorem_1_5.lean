-- Prove2me | solution 1 for SteurerHDX.theorem_1_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:55:12.957558+00:00
-- url     : https://prove2.me/submissions/71b686fc-c1b5-4baa-bce0-1e1990266c5b

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsPartite
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_spectralGap
import Definitions.Def_SteurerHDX_downUp
import Theorems.Thm_SteurerHDX_theorem_2_4
import Theorems.Thm_SteurerHDX_theorem_3_1

section
set_option autoImplicit false
namespace SteurerHDX.Dev.T15
open SteurerHDX Filter Topology

section comb
variable {V : Type} [DecidableEq V]

lemma exists_facet (X : Finset (Finset V)) {d : ℕ} (hX : IsPure X d) (τ : Finset V) (hτ : τ ∈ X) :
    ∃ ρ ∈ faces X d, τ ⊆ ρ := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal (s := X.filter (fun ρ => τ ⊆ ρ))
    ⟨τ, by simp [hτ]⟩
  rw [Finset.mem_filter] at hm
  refine ⟨m, ?_, hm.2⟩
  rw [faces, Finset.mem_filter]
  refine ⟨hm.1, hX.2 m hm.1 ?_⟩
  intro ρ hρ hmρ
  exact (Finset.Subset.antisymm (hmax (Finset.mem_filter.mpr ⟨hρ, hm.2.trans hmρ⟩) hmρ) hmρ)

lemma card_le (X : Finset (Finset V)) (d : ℕ) (hX : IsPure X d) :
    (faces X 1).card ≤ (faces X d).card * d := by
  have h1 : faces X 1 ⊆ ((faces X d).biUnion id).image (fun x => ({x} : Finset V)) := by
    intro τ hτ
    rw [faces, Finset.mem_filter] at hτ
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hτ.2
    obtain ⟨ρ, hρ, hsub⟩ := exists_facet X hX _ hτ.1
    rw [Finset.mem_image]
    exact ⟨x, Finset.mem_biUnion.mpr ⟨ρ, hρ, by simpa using hsub⟩, rfl⟩
  calc (faces X 1).card ≤ (((faces X d).biUnion id).image (fun x => ({x} : Finset V))).card :=
        Finset.card_le_card h1
    _ ≤ ((faces X d).biUnion id).card := Finset.card_image_le
    _ ≤ ∑ σ ∈ faces X d, σ.card := Finset.card_biUnion_le
    _ = (faces X d).card * d := by
        rw [Finset.sum_congr rfl (g := fun _ => d)]
        · simp
        · intro σ hσ
          exact (Finset.mem_filter.mp hσ).2

lemma card_ge (X : Finset (Finset V)) (d : ℕ) (hX : IsPure X d) :
    (faces X d).card * d ≤ (faces X 1).card * degree X d := by
  set U := X.biUnion id with hU
  have hUV : U.card ≤ (faces X 1).card := by
    have : U.card = (U.image (fun x => ({x} : Finset V))).card :=
      (Finset.card_image_of_injective _ (fun a b h => by simpa using h)).symm
    rw [this]
    apply Finset.card_le_card
    intro τ hτ
    rw [Finset.mem_image] at hτ
    obtain ⟨x, hx, rfl⟩ := hτ
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨σ, hσ, hxσ⟩ := hx
    rw [faces, Finset.mem_filter]
    exact ⟨hX.1 σ hσ _ (by simpa using hxσ), by simp⟩
  have hsum : ∑ σ ∈ faces X d, σ.card = ∑ x ∈ U, ((faces X d).filter (fun σ => x ∈ σ)).card := by
    have : ∀ σ ∈ faces X d, σ.card = ∑ x ∈ U, if x ∈ σ then 1 else 0 := by
      intro σ hσ
      have hsub : σ ⊆ U := fun x hx =>
        Finset.mem_biUnion.mpr ⟨σ, (Finset.mem_filter.mp hσ).1, hx⟩
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.card_filter]
  have hbound : ∑ x ∈ U, ((faces X d).filter (fun σ => x ∈ σ)).card ≤ U.card * degree X d := by
    calc _ ≤ ∑ _x ∈ U, degree X d := by
          apply Finset.sum_le_sum
          intro x hx
          exact Finset.le_sup (f := fun x => ((faces X d).filter (fun σ => x ∈ σ)).card) hx
      _ = U.card * degree X d := by simp
  have : ∑ σ ∈ faces X d, σ.card = (faces X d).card * d := by
    rw [Finset.sum_congr rfl (g := fun _ => d)]
    · simp
    · intro σ hσ
      exact (Finset.mem_filter.mp hσ).2
  rw [← this, hsum]
  exact hbound.trans (Nat.mul_le_mul_right _ hUV)

end comb

lemma transfer {ι κ : Type} [Fintype ι] [Fintype κ] (n D : ℕ) (hn : Fintype.card ι = n)
    (hD : Fintype.card κ = D) (v : ι → EuclideanSpace ℝ κ) (β a b : ℝ)
    (h0 : ∀ i k, 0 ≤ v i k) (h1 : ∀ i, ‖v i‖ = 1)
    (h2 : ∀ i j k, ‖v i - v j‖ ^ 2 ≤ ‖v i - v k‖ ^ 2 + ‖v k - v j‖ ^ 2)
    (h3 : (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v i) (v j)| ≤ a)
    (h4 : ∀ A B : Finset ι, Disjoint A B → β * n ≤ A.card → β * n ≤ B.card →
      ∃ i ∈ A, ∃ j ∈ B, ‖v i - v j‖ ^ 2 ≤ b) :
    ∃ w : Fin n → EuclideanSpace ℝ (Fin D),
      (∀ i k, 0 ≤ w i k) ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i j k, ‖w i - w j‖ ^ 2 ≤ ‖w i - w k‖ ^ 2 + ‖w k - w j‖ ^ 2) ∧
      (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (w i) (w j)| ≤ a ∧
      ∀ A B : Finset (Fin n), Disjoint A B → β * n ≤ A.card → β * n ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖w i - w j‖ ^ 2 ≤ b := by
  let eN : Fin n ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  let eD : κ ≃ Fin D := Fintype.equivFinOfCardEq hD
  let T : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin D) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eD
  refine ⟨fun i => T (v (eN i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    have : T (v (eN i)) k = v (eN i) (eD.symm k) := by
      simp [T]
    rw [this]; exact h0 _ _
  · intro i; rw [LinearIsometryEquiv.norm_map]; exact h1 _
  · intro i j k
    simp only [← map_sub, LinearIsometryEquiv.norm_map]
    exact h2 _ _ _
  · refine le_of_eq_of_le ?_ h3
    congr 1
    simp only [LinearIsometryEquiv.inner_map_map]
    rw [← Equiv.sum_comp eN]
    apply Finset.sum_congr rfl; intro i _
    exact (Equiv.sum_comp eN (fun j => |inner ℝ (v (eN i)) (v j)|)).symm ▸ rfl
  · intro A B hAB hA hB
    obtain ⟨i, hi, j, hj, h⟩ := h4 (A.map eN.toEmbedding) (B.map eN.toEmbedding)
      (by simpa using hAB) (by simpa using hA) (by simpa using hB)
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    refine ⟨i', hi', j', hj', ?_⟩
    simp only [← map_sub, LinearIsometryEquiv.norm_map]
    simpa using h


lemma point (β c₁ c₂ C₄ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1 / 2) (hc₁ : 0 < c₁)
    (hX : ∀ k r q : ℕ, 1 ≤ k → k < r → IsPrimePow q → (4 * (2 * k + 1) + 1) ^ 2 ≤ q →
    ∃ X : Finset (Finset ℕ),
      IsPure X (2 * k + 1) ∧ IsPartite X (2 * k + 1) ∧ 2 ≤ (faces X (2 * k + 1)).card ∧
      (q : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces X 1).card : ℝ) ∧
      ((faces X 1).card : ℝ) ≤ (q : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree X (2 * k + 1) : ℝ) ≤ (q : ℝ) ^ (C₄ * r * (2 * k + 1)) ∧
      IsTopLinkExpander X (2 * k + 1) (1 / (2 * (2 * k + 1))) ∧
      lambdaTwo (downUp X (2 * k + 1)) ≤ 1 - 1 / (Real.exp 1 * (2 * k + 1)))
    (k r q : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hq : IsPrimePow q)
    (hq2 : (4 * (2 * k + 1) + 1) ^ 2 ≤ q) :
    ∃ (n D : ℕ) (Δ : ℝ), 2 ≤ n ∧ 1 ≤ Δ ∧
      Real.log Δ ≤ C₄ * r * (2 * k + 1) * Real.log q ∧
      c₁ * (r : ℝ) ^ 2 * Real.log q - Real.log (2 * k + 1) ≤ Real.log n ∧
      Real.log n ≤ (c₂ * (r : ℝ) ^ 2 + C₄ * r * (2 * k + 1)) * Real.log q ∧
      ∃ w : Fin n → EuclideanSpace ℝ (Fin D),
      (∀ i k, 0 ≤ w i k) ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i j k, ‖w i - w j‖ ^ 2 ≤ ‖w i - w k‖ ^ 2 + ‖w k - w j‖ ^ 2) ∧
      (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (w i) (w j)| ≤ Δ / n ∧
      ∀ A B : Finset (Fin n), Disjoint A B → β * n ≤ A.card → β * n ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖w i - w j‖ ^ 2 ≤
          2 / (β * Real.sqrt (1 / Real.exp 1 * (2 * k + 1 : ℕ))) := by
  obtain ⟨X, hpure, -, hcard, hV1, hV2, hdeg, -, hlam⟩ := hX k r q hk hkr hq hq2
  set d : ℕ := 2 * k + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (d : ℝ) = 2 * k + 1 := by rw [hd]; push_cast; ring
  have hqR : (1 : ℝ) < q := by
    have : 1 < q := lt_of_lt_of_le (by nlinarith) hq2
    exact_mod_cast this
  have hL : 0 < Real.log q := Real.log_pos hqR
  have hgap : 1 / Real.exp 1 / d ≤ spectralGap (downUp X d) := by
    unfold spectralGap
    have : 1 / Real.exp 1 / (d : ℝ) = 1 / (Real.exp 1 * (2 * k + 1)) := by
      rw [← hdR]; field_simp
    rw [this]; linarith
  have h31 := theorem_3_1 X d (1 / Real.exp 1) hpure hcard (by positivity) hgap
  obtain ⟨v, h0, h1, h2, h3, h4⟩ := h31
  set n := (faces X d).card with hn
  have hcomb1 := card_le X d hpure
  have hcomb2 := card_ge X d hpure
  have hn2 : 2 ≤ n := hcard
  set V := (faces X 1).card with hV
  set Dg := degree X d with hDg
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hV1
  have hVn : (V : ℝ) ≤ n * d := by exact_mod_cast hcomb1
  have hnV : (n : ℝ) * d ≤ V * Dg := by exact_mod_cast hcomb2
  have hDgpos : (1 : ℝ) ≤ Dg := by
    have h : 0 < Dg := by
      rcases Nat.eq_zero_or_pos Dg with h | h
      · rw [h, mul_zero] at hcomb2
        have hp : 0 < n * d := Nat.mul_pos (by omega) hd1
        exact absurd hp (Nat.not_lt.mpr hcomb2)
      · exact h
    exact_mod_cast h
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogDg : Real.log Dg ≤ C₄ * r * (2 * k + 1) * Real.log q := by
    calc Real.log Dg ≤ Real.log ((q : ℝ) ^ (C₄ * r * (2 * k + 1))) :=
          Real.log_le_log (by linarith) hdeg
      _ = _ := Real.log_rpow hqpos _
  have hlogV1 : c₁ * (r : ℝ) ^ 2 * Real.log q ≤ Real.log V := by
    calc c₁ * (r : ℝ) ^ 2 * Real.log q = Real.log ((q : ℝ) ^ (c₁ * (r : ℝ) ^ 2)) :=
          (Real.log_rpow hqpos _).symm
      _ ≤ _ := Real.log_le_log (Real.rpow_pos_of_pos hqpos _) hV1
  have hlogV2 : Real.log V ≤ c₂ * (r : ℝ) ^ 2 * Real.log q := by
    calc Real.log V ≤ Real.log ((q : ℝ) ^ (c₂ * (r : ℝ) ^ 2)) :=
          Real.log_le_log hVpos hV2
      _ = _ := Real.log_rpow hqpos _
  refine ⟨n, V, Dg, hn2, hDgpos, hlogDg, ?_, ?_, ?_⟩
  · have : Real.log V ≤ Real.log n + Real.log d := by
      rw [← Real.log_mul hnpos.ne' hdpos.ne']
      exact Real.log_le_log hVpos hVn
    rw [hdR] at this
    linarith
  · have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have : (n : ℝ) ≤ V * Dg := by nlinarith
    have h' : Real.log n ≤ Real.log V + Real.log Dg := by
      rw [← Real.log_mul hVpos.ne' (by linarith)]
      exact Real.log_le_log hnpos this
    nlinarith
  · have hcn : Fintype.card (faces X d) = n := Fintype.card_coe _
    have hcV : Fintype.card (faces X 1) = V := Fintype.card_coe _
    obtain ⟨w, hw⟩ := transfer (ι := faces X d) (κ := faces X 1) n V hcn hcV v β
      ((Dg : ℝ) / n) (2 / (β * Real.sqrt (1 / Real.exp 1 * (d : ℝ)))) h0 h1 h2 h3
      (fun A B hAB hA hB => h4 β hβ0 (by linarith) A B hAB hA hB)
    exact ⟨w, hw⟩


lemma tendsto_aux (a b : ℝ) :
    Tendsto (fun x : ℝ => (a + b * Real.log x) / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => a * x⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul a
  have h2 : Tendsto (fun x : ℝ => b * (Real.log x / x)) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).const_mul b
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma analytic (c₁ c₂ C₄ K : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hC : 0 < C₄)
    (d s L lg lΔ : ℕ → ℝ) (hd : Tendsto d atTop atTop) (hd3 : ∀ t, 3 ≤ d t)
    (hs1 : ∀ t, Real.log (d t) ≤ s t) (hs2 : ∀ t, s t ≤ Real.log (d t) + 1)
    (hL1 : ∀ t, 1 ≤ L t) (hL2 : ∀ t, L t ≤ 5 + 2 * Real.log (d t))
    (hΔ0 : ∀ t, 0 ≤ lΔ t) (hΔ1 : ∀ t, lΔ t ≤ C₄ * (d t * s t) * d t * L t)
    (hn1 : ∀ t, c₁ * (d t * s t) ^ 2 * L t - Real.log (d t) ≤ lg t)
    (hn2 : ∀ t, lg t ≤ (c₂ * (d t * s t) ^ 2 + C₄ * (d t * s t) * d t) * L t) :
    Tendsto lg atTop atTop ∧ Tendsto (fun t => lΔ t / lg t) atTop (𝓝 0) ∧
    Tendsto (fun t => 1 / 4 + (K - Real.log (d t) / 2) / Real.log (lg t)) atTop (𝓝 0) := by
  have hℓ : Tendsto (fun t => Real.log (d t)) atTop atTop := Real.tendsto_log_atTop.comp hd
  have hs : Tendsto s atTop atTop := tendsto_atTop_mono hs1 hℓ
  have hℓ1 : ∀ t, 1 ≤ Real.log (d t) := fun t =>
    one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (hd3 t))
  have hs1' : ∀ t, 1 ≤ s t := fun t => (hℓ1 t).trans (hs1 t)
  have hdpos : ∀ t, 0 < d t := fun t => by linarith [hd3 t]
  -- eventually: d large
  have hev : ∀ᶠ t in atTop, 2 / c₁ ≤ d t ∧ -Real.log (c₁ / 2) + 1 ≤ Real.log (d t) := by
    filter_upwards [hd.eventually_ge_atTop (2 / c₁),
      hℓ.eventually_ge_atTop (-Real.log (c₁ / 2) + 1)] with t h1 h2 using ⟨h1, h2⟩
  -- X := (d s)^2 L
  have hX : ∀ t, d t ^ 2 ≤ (d t * s t) ^ 2 * L t := by
    intro t
    have h1 := hs1' t
    have h2 := hL1 t
    have : 1 ≤ s t ^ 2 * L t := by nlinarith
    calc d t ^ 2 = d t ^ 2 * 1 := by ring
      _ ≤ d t ^ 2 * (s t ^ 2 * L t) := by gcongr
      _ = _ := by ring
  have hlow : ∀ t, 2 / c₁ ≤ d t → (c₁ / 2) * ((d t * s t) ^ 2 * L t) ≤ lg t := by
    intro t ht
    have h1 : Real.log (d t) ≤ d t := Real.log_le_self (hdpos t).le
    have h2 : d t ≤ (c₁ / 2) * d t ^ 2 := by
      have : 2 / c₁ * (c₁ / 2) = 1 := by field_simp
      nlinarith [hdpos t, mul_le_mul_of_nonneg_right ht (mul_nonneg (by positivity) (hdpos t).le : 0 ≤ (c₁ / 2) * d t)]
    have h3 := hX t
    have h4 := hn1 t
    nlinarith
  have hup : ∀ t, lg t ≤ (c₂ + C₄) * ((d t * s t) ^ 2 * L t) := by
    intro t
    refine (hn2 t).trans ?_
    have h1 := hs1' t
    have h2 : d t ≤ d t * s t := by nlinarith [hdpos t]
    have hL0 : 0 ≤ L t := by linarith [hL1 t]
    have : C₄ * (d t * s t) * d t ≤ C₄ * (d t * s t) ^ 2 := by
      have : (d t * s t) * d t ≤ (d t * s t) ^ 2 := by nlinarith [hdpos t]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hL0]
  -- Part A
  have hA : Tendsto lg atTop atTop := by
    have h1 : Tendsto (fun t => (c₁ / 2) * d t ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hd |>.const_mul_atTop (by positivity)
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [hev] with t ht
    refine le_trans ?_ (hlow t ht.1)
    gcongr
    exact hX t
  refine ⟨hA, ?_, ?_⟩
  · -- Part B
    have hb : ∀ᶠ t in atTop, lΔ t / lg t ≤ (2 * C₄ / c₁) / s t := by
      filter_upwards [hev] with t ht
      have hlg := hlow t ht.1
      have hXp : 0 < (d t * s t) ^ 2 * L t := by
        have := hX t; nlinarith [hdpos t]
      have hlgpos : 0 < lg t := lt_of_lt_of_le (mul_pos (by positivity) hXp) hlg
      have hspos : 0 < s t := by linarith [hs1' t]
      rw [div_le_div_iff₀ hlgpos hspos]
      have e1 : lΔ t * s t ≤ C₄ * (d t * s t) ^ 2 * L t := by
        have := mul_le_mul_of_nonneg_right (hΔ1 t) hspos.le
        nlinarith
      have e2 : 2 * C₄ / c₁ * ((c₁ / 2) * ((d t * s t) ^ 2 * L t)) =
          C₄ * ((d t * s t) ^ 2 * L t) := by field_simp
      calc lΔ t * s t ≤ C₄ * ((d t * s t) ^ 2 * L t) := by linarith
        _ = 2 * C₄ / c₁ * ((c₁ / 2) * ((d t * s t) ^ 2 * L t)) := e2.symm
        _ ≤ _ := by gcongr
    refine squeeze_zero' ?_ hb ?_
    · filter_upwards [hev] with t ht
      have hlgpos : 0 < lg t := lt_of_lt_of_le (mul_pos (by positivity) (by
        have := hX t; have := hdpos t; nlinarith)) (hlow t ht.1)
      exact div_nonneg (hΔ0 t) hlgpos.le
    · exact tendsto_const_nhds.div_atTop hs
  · -- Part C
    set m0 := Real.log (c₁ / 2) with hm0
    set M := Real.log (c₂ + C₄) + 2 * Real.log 2 + Real.log 7 with hM
    set P := (|m0| + |M|) / 4 + |K| with hP
    have hbound : ∀ᶠ t in atTop,
        |1 / 4 + (K - Real.log (d t) / 2) / Real.log (lg t)| ≤
          (P + (3 / 4) * Real.log (Real.log (d t))) / Real.log (d t) := by
      filter_upwards [hev] with t ht
      have hℓ1' := hℓ1 t
      have hlg := hlow t ht.1
      have hdp := hdpos t
      have hXp : 0 < (d t * s t) ^ 2 * L t := by
        have := hX t; nlinarith
      have hlgpos : 0 < lg t := lt_of_lt_of_le (mul_pos (by positivity) hXp) hlg
      have hlgup := hup t
      have hs1t := hs1' t
      have hL0 : 0 < L t := by linarith [hL1 t]
      have hspos : 0 < s t := by linarith
      have hc2 : 0 < c₂ + C₄ := by linarith
      -- lower bound for ll
      have hll1 : m0 + 2 * Real.log (d t) ≤ Real.log (lg t) := by
        have h := Real.log_le_log (mul_pos (by positivity) (pow_pos hdp 2))
          (le_trans (mul_le_mul_of_nonneg_left (hX t) (by positivity)) hlg)
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
        push_cast at h
        linarith
      -- upper bound for ll
      have hll2 : Real.log (lg t) ≤ M + 2 * Real.log (d t) + 3 * Real.log (Real.log (d t)) := by
        have h := Real.log_le_log hlgpos hlgup
        rw [Real.log_mul hc2.ne' hXp.ne', Real.log_mul (by positivity) hL0.ne',
          Real.log_pow, Real.log_mul hdp.ne' hspos.ne'] at h
        push_cast at h
        have hl1 : Real.log (s t) ≤ Real.log 2 + Real.log (Real.log (d t)) := by
          rw [← Real.log_mul (by norm_num) (by linarith)]
          exact Real.log_le_log hspos (by linarith [hs2 t])
        have hl2 : Real.log (L t) ≤ Real.log 7 + Real.log (Real.log (d t)) := by
          rw [← Real.log_mul (by norm_num) (by linarith)]
          exact Real.log_le_log hL0 (by linarith [hL2 t])
        rw [hM]
        linarith
      have hlogℓ : 0 ≤ Real.log (Real.log (d t)) := Real.log_nonneg hℓ1'
      have hllpos : Real.log (d t) ≤ Real.log (lg t) := by linarith [ht.2]
      have hllp : 0 < Real.log (lg t) := by linarith
      have heq : 1 / 4 + (K - Real.log (d t) / 2) / Real.log (lg t) =
          ((Real.log (lg t) - 2 * Real.log (d t)) / 4 + K) / Real.log (lg t) := by
        field_simp
        ring
      rw [heq, abs_div, abs_of_pos hllp]
      have hnum : |(Real.log (lg t) - 2 * Real.log (d t)) / 4 + K| ≤
          P + (3 / 4) * Real.log (Real.log (d t)) := by
        have a1 := abs_nonneg m0
        have a2 := abs_nonneg M
        have a3 := abs_nonneg K
        have b1 := le_abs_self m0
        have b2 := le_abs_self M
        have b3 := neg_abs_le K
        have b4 := le_abs_self K
        have b5 := neg_abs_le m0
        rw [abs_le]
        constructor <;> nlinarith
      calc _ ≤ (P + (3 / 4) * Real.log (Real.log (d t))) / Real.log (lg t) := by gcongr
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by linarith [abs_nonneg K, abs_nonneg m0, abs_nonneg M]) (by linarith) hllpos
    have hlim := (tendsto_aux P (3 / 4)).comp hℓ
    exact squeeze_zero_norm' hbound hlim


def dN (t : ℕ) : ℕ := 2 * (t + 1) + 1
noncomputable def sN (t : ℕ) : ℕ := ⌈Real.log (dN t : ℝ)⌉₊
noncomputable def rN (t : ℕ) : ℕ := dN t * sN t
@[irreducible] def qN (t : ℕ) : ℕ := 2 ^ Nat.clog 2 ((4 * dN t + 1) ^ 2)

lemma qN_prop (t : ℕ) : IsPrimePow (qN t) ∧ (4 * (2 * (t + 1) + 1) + 1) ^ 2 ≤ qN t ∧
    (qN t : ℝ) < 64 * (dN t : ℝ) ^ 2 := by
  have hd1 : 1 ≤ dN t := by unfold dN; omega
  have hx4 : 5 ≤ 4 * dN t + 1 := by omega
  have hx : 1 < (4 * dN t + 1) ^ 2 := by
    have := Nat.pow_le_pow_left hx4 2
    omega
  have hpos : Nat.clog 2 ((4 * dN t + 1) ^ 2) ≠ 0 := by
    have := Nat.clog_pos (b := 2) (by norm_num) hx
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hq : qN t = 2 ^ (j + 1) := by unfold qN; rw [hj]
  refine ⟨by rw [hq]; exact Nat.prime_two.isPrimePow.pow (by omega), ?_, ?_⟩
  · unfold qN; exact Nat.le_pow_clog (b := 2) (by norm_num) _
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hx
  rw [hj] at h1
  simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel, Nat.succ_eq_add_one] at h1
  have h3 : qN t < 2 * (4 * dN t + 1) ^ 2 := by rw [hq, pow_succ]; omega
  generalize qN t = q at h3 ⊢
  generalize dN t = d at h3 hd1 ⊢
  have h4 : (q : ℝ) < 2 * (4 * (d : ℝ) + 1) ^ 2 := by exact_mod_cast h3
  have h5 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  nlinarith


lemma logB (β d : ℝ) (hβ : 0 < β) (hd : 0 < d) :
    Real.log (2 / (β * Real.sqrt (1 / Real.exp 1 * d))) =
      Real.log 2 - Real.log β + 1 / 2 - Real.log d / 2 := by
  have h1 : 0 < 1 / Real.exp 1 * d := by positivity
  have h2 : 0 < Real.sqrt (1 / Real.exp 1 * d) := Real.sqrt_pos.mpr h1
  rw [Real.log_div (by norm_num) (by positivity), Real.log_mul hβ.ne' h2.ne', Real.log_sqrt h1.le,
    Real.log_mul (by positivity) hd.ne', one_div, Real.log_inv, Real.log_exp]
  ring

lemma main (β c₁ c₂ C₄ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1 / 2) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hC : 0 < C₄)
    (hX : ∀ k r q : ℕ, 1 ≤ k → k < r → IsPrimePow q → (4 * (2 * k + 1) + 1) ^ 2 ≤ q →
    ∃ X : Finset (Finset ℕ),
      IsPure X (2 * k + 1) ∧ IsPartite X (2 * k + 1) ∧ 2 ≤ (faces X (2 * k + 1)).card ∧
      (q : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces X 1).card : ℝ) ∧
      ((faces X 1).card : ℝ) ≤ (q : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree X (2 * k + 1) : ℝ) ≤ (q : ℝ) ^ (C₄ * r * (2 * k + 1)) ∧
      IsTopLinkExpander X (2 * k + 1) (1 / (2 * (2 * k + 1))) ∧
      lambdaTwo (downUp X (2 * k + 1)) ≤ 1 - 1 / (Real.exp 1 * (2 * k + 1))) :
    ∃ (N D : ℕ → ℕ) (v : (m : ℕ) → Fin (N m) → EuclideanSpace ℝ (Fin (D m))) (e₁ e₂ : ℕ → ℝ),
      StrictMono N ∧ Tendsto e₁ atTop (𝓝 0) ∧ Tendsto e₂ atTop (𝓝 0) ∧
      ∀ m, 0 < N m ∧
        (∀ i k, 0 ≤ v m i k) ∧ (∀ i, ‖v m i‖ = 1) ∧
        (∀ i j k, ‖v m i - v m j‖ ^ 2 ≤ ‖v m i - v m k‖ ^ 2 + ‖v m k - v m j‖ ^ 2) ∧
        (1 / (N m : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v m i) (v m j)| ≤ (N m : ℝ) ^ (-1 + e₁ m) ∧
        ∀ A B : Finset (Fin (N m)), Disjoint A B →
          β * N m ≤ A.card → β * N m ≤ B.card →
          ∃ i ∈ A, ∃ j ∈ B,
            ‖v m i - v m j‖ ^ 2 ≤ 1 * Real.log (N m) ^ (-(1 / 4 : ℝ) + e₂ m) := by
  have hdR : ∀ t, (dN t : ℝ) = 2 * ((t + 1 : ℕ) : ℝ) + 1 := fun t => by unfold dN; push_cast; ring
  have hd1 : ∀ t, (3 : ℝ) ≤ dN t := fun t => by exact_mod_cast (by unfold dN; omega : 3 ≤ dN t)
  have hlogd : ∀ t, 1 ≤ Real.log (dN t : ℝ) := fun t =>
    one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (hd1 t))
  have key : ∀ t : ℕ, ∃ (n D : ℕ) (Δ : ℝ), 2 ≤ n ∧ 1 ≤ Δ ∧
      Real.log Δ ≤ C₄ * (rN t : ℝ) * (dN t : ℝ) * Real.log (qN t) ∧
      c₁ * (rN t : ℝ) ^ 2 * Real.log (qN t) - Real.log (dN t : ℝ) ≤ Real.log n ∧
      Real.log n ≤ (c₂ * (rN t : ℝ) ^ 2 + C₄ * (rN t : ℝ) * (dN t : ℝ)) * Real.log (qN t) ∧
      ∃ w : Fin n → EuclideanSpace ℝ (Fin D),
      (∀ i k, 0 ≤ w i k) ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i j k, ‖w i - w j‖ ^ 2 ≤ ‖w i - w k‖ ^ 2 + ‖w k - w j‖ ^ 2) ∧
      (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (w i) (w j)| ≤ Δ / n ∧
      ∀ A B : Finset (Fin n), Disjoint A B → β * n ≤ A.card → β * n ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖w i - w j‖ ^ 2 ≤ 2 / (β * Real.sqrt (1 / Real.exp 1 * (dN t : ℝ))) := by
    intro t
    obtain ⟨hq, hq2, -⟩ := qN_prop t
    have hs : 0 < sN t := by
      unfold sN
      rw [Nat.ceil_pos]
      linarith [hlogd t]
    have hkr : t + 1 < rN t := by
      have h1 : dN t ≤ rN t := Nat.le_mul_of_pos_right _ hs
      have h2 : dN t = 2 * t + 3 := by unfold dN; omega
      omega
    have := point β c₁ c₂ C₄ hβ0 hβ1 hc₁ hX (t + 1) (rN t) (qN t) (by omega) hkr hq hq2
    rw [← hdR t] at this
    exact this
  choose n D Δ hn2 hΔ1 hΔlog hnlow hnup w hw0 hw1 hw2 hw3 hw4 using key
  have hrR : ∀ t, (rN t : ℝ) = (dN t : ℝ) * (sN t : ℝ) := fun t => by unfold rN; push_cast; ring
  have hdT : Tendsto (fun t => (dN t : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun t => ?_) tendsto_id)
    unfold dN; simp only [id]; omega
  have hqprop : ∀ t, (3 : ℝ) ≤ qN t := fun t => by
    have h := (qN_prop t).2.1
    have : 3 ≤ qN t := by
      have h2 := Nat.pow_le_pow_left (by omega : 5 ≤ 4 * (2 * (t + 1) + 1) + 1) 2
      omega
    exact_mod_cast this
  have hnR : ∀ t, (2 : ℝ) ≤ n t := fun t => by exact_mod_cast hn2 t
  obtain ⟨hlgT, he1, he2⟩ := analytic c₁ c₂ C₄ (Real.log 2 - Real.log β + 1 / 2) hc₁ hc₂ hC
    (fun t => (dN t : ℝ)) (fun t => (sN t : ℝ)) (fun t => Real.log (qN t))
    (fun t => Real.log (n t)) (fun t => Real.log (Δ t)) hdT hd1
    (fun t => Nat.le_ceil _)
    (fun t => (Nat.ceil_lt_add_one (by linarith [hlogd t])).le)
    (fun t => one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (hqprop t)))
    (fun t => by
      have h := (qN_prop t).2.2
      have hqp : (0 : ℝ) < qN t := by linarith [hqprop t]
      have h1 : Real.log (qN t) ≤ Real.log (64 * (dN t : ℝ) ^ 2) :=
        Real.log_le_log hqp h.le
      have hdp : (0 : ℝ) < dN t := by linarith [hd1 t]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      have h64 : Real.log 64 < 5 := by
        have : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_lt_d9
        linarith
      push_cast at h1
      linarith)
    (fun t => Real.log_nonneg (hΔ1 t))
    (fun t => by have := hΔlog t; rw [hrR] at this; simpa using this)
    (fun t => by have := hnlow t; rw [hrR] at this; simpa using this)
    (fun t => by have := hnup t; rw [hrR] at this; simpa using this)
  have hnT : Tendsto n atTop atTop := by
    have h : Tendsto (fun t => (n t : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun t => Real.log_le_self (by have := hnR t; linarith)) hlgT
    exact tendsto_natCast_atTop_iff.mp h
  obtain ⟨t0, ht0⟩ := eventually_atTop.mp (hlgT.eventually_gt_atTop 1)
  have hg : ∀ t, ∃ t', t < t' ∧ n t < n t' := fun t =>
    ((eventually_gt_atTop t).and (hnT.eventually_gt_atTop (n t))).exists
  choose g hg1 hg2 using hg
  let φ : ℕ → ℕ := fun m => Nat.rec t0 (fun _ x => g x) m
  have hφs : StrictMono φ := strictMono_nat_of_lt_succ (fun m => hg1 (φ m))
  have hφn : StrictMono (fun m => n (φ m)) := strictMono_nat_of_lt_succ (fun m => hg2 (φ m))
  have hφ0 : ∀ m, t0 ≤ φ m := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ m ih => exact ih.trans (hg1 (φ m)).le
  refine ⟨fun m => n (φ m), fun m => D (φ m), fun m => w (φ m),
    fun m => Real.log (Δ (φ m)) / Real.log (n (φ m)),
    fun m => 1 / 4 + (Real.log 2 - Real.log β + 1 / 2 - Real.log (dN (φ m) : ℝ) / 2) /
      Real.log (Real.log (n (φ m))),
    hφn, he1.comp hφs.tendsto_atTop, he2.comp hφs.tendsto_atTop, fun m => ?_⟩
  have ht := ht0 (φ m) (hφ0 m)
  beta_reduce
  generalize φ m = t at ht ⊢
  have hnp : (0 : ℝ) < n t := by have := hnR t; linarith
  have hlp : 0 < Real.log (n t) := by linarith
  have hll : 0 < Real.log (Real.log (n t)) := Real.log_pos ht
  have hΔp : 0 < Δ t := by have := hΔ1 t; linarith
  refine ⟨by have := hn2 t; omega, hw0 t, hw1 t, hw2 t, ?_, ?_⟩
  · refine (hw3 t).trans (le_of_eq ?_)
    show Δ t / n t = (n t : ℝ) ^ (-1 + Real.log (Δ t) / Real.log (n t))
    rw [Real.rpow_add hnp, Real.rpow_neg_one, Real.rpow_def_of_pos hnp]
    have : Real.log (n t) * (Real.log (Δ t) / Real.log (n t)) = Real.log (Δ t) := by
      field_simp
    rw [this, Real.exp_log hΔp]; ring
  · intro A B hAB hA hB
    obtain ⟨i, hi, j, hj, h⟩ := hw4 t A B hAB hA hB
    refine ⟨i, hi, j, hj, h.trans (le_of_eq ?_)⟩
    show 2 / (β * Real.sqrt (1 / Real.exp 1 * (dN t : ℝ))) = 1 * Real.log (n t) ^
      (-(1 / 4 : ℝ) + (1 / 4 + (Real.log 2 - Real.log β + 1 / 2 - Real.log (dN t : ℝ) / 2) /
        Real.log (Real.log (n t))))
    have hdp : (0 : ℝ) < dN t := by linarith [hd1 t]
    have hBp : 0 < 2 / (β * Real.sqrt (1 / Real.exp 1 * (dN t : ℝ))) := by
      have : 0 < Real.sqrt (1 / Real.exp 1 * (dN t : ℝ)) := Real.sqrt_pos.mpr (by positivity)
      positivity
    rw [one_mul, Real.rpow_def_of_pos hlp]
    have e1 : -(1 / 4 : ℝ) + (1 / 4 + (Real.log 2 - Real.log β + 1 / 2 - Real.log (dN t : ℝ) / 2) /
        Real.log (Real.log (n t))) =
        (Real.log 2 - Real.log β + 1 / 2 - Real.log (dN t : ℝ) / 2) /
        Real.log (Real.log (n t)) := by ring
    rw [e1, mul_div_cancel₀ _ hll.ne', ← logB β (dN t : ℝ) hβ0 hdp, Real.exp_log hBp]

end SteurerHDX.Dev.T15

namespace SteurerHDX
open Filter Topology
theorem chk_theorem_1_5 :
    ∀ β : ℝ, 0 < β → β < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ (N D : ℕ → ℕ) (v : (m : ℕ) → Fin (N m) → EuclideanSpace ℝ (Fin (D m))) (e₁ e₂ : ℕ → ℝ),
      StrictMono N ∧ Tendsto e₁ atTop (𝓝 0) ∧ Tendsto e₂ atTop (𝓝 0) ∧
      ∀ m, 0 < N m ∧
        (∀ i k, 0 ≤ v m i k) ∧ (∀ i, ‖v m i‖ = 1) ∧
        (∀ i j k, ‖v m i - v m j‖ ^ 2 ≤ ‖v m i - v m k‖ ^ 2 + ‖v m k - v m j‖ ^ 2) ∧
        (1 / (N m : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v m i) (v m j)| ≤ (N m : ℝ) ^ (-1 + e₁ m) ∧
        ∀ A B : Finset (Fin (N m)), Disjoint A B →
          β * N m ≤ A.card → β * N m ≤ B.card →
          ∃ i ∈ A, ∃ j ∈ B,
            ‖v m i - v m j‖ ^ 2 ≤ C * Real.log (N m) ^ (-(1 / 4 : ℝ) + e₂ m) := by
  intro β hβ0 hβ1
  obtain ⟨c₁, c₂, C₄, hc₁, hc₂, hC, hX⟩ := theorem_2_4
  exact ⟨1, one_pos, Dev.T15.main β c₁ c₂ C₄ hβ0 hβ1 hc₁ hc₂ hC hX⟩

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_theorem_1_5 := @SteurerHDX.chk_theorem_1_5
