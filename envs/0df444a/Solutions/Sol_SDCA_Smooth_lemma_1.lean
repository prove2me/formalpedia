-- Prove2me | solution 1 for SDCA.Smooth.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:44:40.550217+00:00
-- url     : https://prove2.me/submissions/c065fee8-ebb8-4f78-8616-8e606ebe1bb1

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

set_option autoImplicit false
open scoped InnerProductSpace
open SDCA.Smooth
open SDCA.Lipschitz (conj)

theorem sds_conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

theorem sds_conj_real (ψ : ℝ → ℝ) (u : ℝ) (h : conj ψ u ≠ ⊤) : ∃ c : ℝ, conj ψ u = (c : EReal) := by
  lift conj ψ u to ℝ using ⟨h, sds_conj_ne_bot ψ u⟩ with c hc
  exact ⟨c, rfl⟩

/-- Fenchel equality at a subgradient. -/
theorem sds_conj_subgrad (ψ : ℝ → ℝ) (a g : ℝ) (h : ∀ z : ℝ, ψ a + g * (z - a) ≤ ψ z) :
    conj ψ g = ((a * g - ψ a : ℝ) : EReal) := by
  apply le_antisymm
  · unfold conj
    refine iSup_le (fun z => ?_)
    rw [EReal.coe_le_coe_iff]
    have := h z
    linarith
  · exact le_iSup (fun z : ℝ => ((z * g - ψ z : ℝ) : EReal)) a

theorem sds_norm_expand {d : ℕ} (w y : EuclideanSpace ℝ (Fin d)) (c δ : ℝ) :
    ‖w + c • (δ • y)‖ ^ 2 = ‖w‖ ^ 2 + 2 * (c * δ) * inner ℝ w y + (c * δ) ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, inner_smul_right, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem sds_eq10 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (i : Fin n) (hfeas : SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤)
    (γ : ℝ) (hγ : 0 ≤ γ) (hsc : ConjStronglyConvex (φ i) γ)
    (u : ℝ)
    (hu : ∀ z : ℝ, φ i ⟪wOf lam x α, x i⟫_ℝ + (-u) * (z - ⟪wOf lam x α, x i⟫_ℝ) ≤ φ i z)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    coordObj lam x φ α i (Δ α i) - coordObj lam x φ α i 0 ≥
      ((s : ℝ) : EReal) *
        (((φ i ⟪wOf lam x α, x i⟫_ℝ : ℝ) : EReal) + SDCA.Lipschitz.conj (φ i) (-α i) +
          ((α i * ⟪wOf lam x α, x i⟫_ℝ +
              (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  set w := wOf lam x α with hw
  set a : ℝ := ⟪w, x i⟫_ℝ with ha
  obtain ⟨c0, hc0⟩ := sds_conj_real _ _ hfeas
  have hcu : conj (φ i) (-u) = ((a * (-u) - φ i a : ℝ) : EReal) := sds_conj_subgrad _ a (-u) hu
  set δ : ℝ := s * (u - α i) with hδ
  -- strong convexity at r = s
  have hsc0 := hsc (-u) (-α i) s ⟨hs0, hs1⟩
  have harg : s * -u + (1 - s) * -α i = -(α i + δ) := by rw [hδ]; ring
  rw [harg, hcu, hc0] at hsc0
  have hreal : -(((s : ℝ) : EReal) * ((a * (-u) - φ i a : ℝ) : EReal)) -
      ((1 - s : ℝ) : EReal) * (c0 : EReal) +
        ((γ * s * (1 - s) / 2 * (-u - -α i) ^ 2 : ℝ) : EReal) =
      ((-(s * (a * (-u) - φ i a)) - (1 - s) * c0 + γ * s * (1 - s) / 2 * (-u - -α i) ^ 2 : ℝ) : EReal) := by
    simp only [EReal.coe_sub, EReal.coe_add, EReal.coe_mul, EReal.coe_neg]
  rw [hreal] at hsc0
  have hsc1 : conj (φ i) (-(α i + δ)) ≤
      ((-(-(s * (a * (-u) - φ i a)) - (1 - s) * c0 + γ * s * (1 - s) / 2 * (-u - -α i) ^ 2) : ℝ) : EReal) := by
    have := EReal.neg_le_neg_iff.mpr hsc0
    rw [neg_neg, ← EReal.coe_neg] at this
    exact this
  -- the right side is a real number
  have hR1 : conj (φ i) (-(α i + δ)) ≤
      ((s * (a * (-u) - φ i a) + (1 - s) * c0 - γ * s * (1 - s) / 2 * (u - α i) ^ 2 : ℝ) : EReal) := by
    refine hsc1.trans (le_of_eq ?_)
    congr 1
    have : ((-u) - (-α i)) ^ 2 = (u - α i) ^ 2 := by ring
    rw [this]; ring
  obtain ⟨c2, hc2⟩ := sds_conj_real (φ i) (-(α i + δ))
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hR1)
  rw [hc2, EReal.coe_le_coe_iff] at hR1
  -- coordinate objective at δ and at 0
  have hobjδ : coordObj lam x φ α i δ =
      ((-c2 - lam * n / 2 * ‖w + (lam * n)⁻¹ • (δ • x i)‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    rw [hc2, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hobj0 : coordObj lam x φ α i 0 = ((-c0 - lam * n / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    simp only [add_zero, zero_smul, smul_zero]
    rw [hc0, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hmax := hΔ α i δ
  have h1 : coordObj lam x φ α i (Δ α i) - coordObj lam x φ α i 0 ≥
      coordObj lam x φ α i δ - coordObj lam x φ α i 0 := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add hmax le_rfl
  refine le_trans ?_ h1
  rw [hobjδ, hobj0, ← EReal.coe_sub]
  have hrhs : ((s : ℝ) : EReal) *
        (((φ i a : ℝ) : EReal) + conj (φ i) (-α i) +
          ((α i * a + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)) =
      ((s * (φ i a + c0 + (α i * a
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2)) : ℝ) : EReal) := by
    rw [hc0, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul]
  rw [hrhs, EReal.coe_le_coe_iff]
  rw [sds_norm_expand w (x i) ((lam * n)⁻¹) δ]
  have hδa : δ = s * (u - α i) := rfl
  have e1 : lam * n / 2 * (‖w‖ ^ 2 + 2 * ((lam * n)⁻¹ * δ) * a + ((lam * n)⁻¹ * δ) ^ 2 * ‖x i‖ ^ 2)
      = lam * n / 2 * ‖w‖ ^ 2 + δ * a + δ ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) := by
    field_simp
  rw [e1]
  have e2 : (s * (u - α i)) ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) =
      s * (s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 := by ring
  rw [hδa] at *
  rw [e2]
  linarith [hR1]

theorem sds_coe_esum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  let g : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  exact map_sum g _ _


theorem solution {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (γ : ℝ) (hγ : 0 ≤ γ) (hsc : ∀ i, ConjStronglyConvex (φ i) γ)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (u : Fin n → ℝ → ℝ) (hu : ∀ i a z, φ i a + (-(u i a)) * (z - a) ≤ φ i z)
    (α : Fin n → ℝ) (hfeas : ∀ i, SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ i, dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i) ≠ ⊥) ∧
    (1 / (n : ℝ)) * ∑ i, (dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i)).toReal - (dual lam x φ α).toReal ≥
      s / n * (primal lam x φ (wOf lam x α) - (dual lam x φ α).toReal) -
        (s / n) ^ 2 *
          ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s) *
            (u i ⟪wOf lam x α, x i⟫_ℝ - α i) ^ 2) / (2 * lam) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  have hs0' : s ≠ 0 := hs0.ne'
  set w := wOf lam x α with hw
  have hreal : ∀ i, ∃ c : ℝ, SDCA.Lipschitz.conj (φ i) (-α i) = (c : EReal) :=
    fun i => sds_conj_real _ _ (hfeas i)
  choose c hc using hreal
  have hD0 : dual lam x φ α = ((1 / (n : ℝ) * ∑ i, (-c i) - lam / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
    unfold dual
    rw [← hw]
    simp only [hc]
    simp only [EReal.coe_sub, EReal.coe_mul, sds_coe_esum, EReal.coe_neg]
  have hD0r : (dual lam x φ α).toReal = 1 / (n : ℝ) * ∑ i, (-c i) - lam / 2 * ‖w‖ ^ 2 := by
    rw [hD0]; rfl
  have hinner : ∑ i, α i * ⟪w, x i⟫_ℝ = lam * n * ‖w‖ ^ 2 := by
    have h1 : (lam * n) • w = ∑ i, α i • x i := by
      rw [hw]; unfold wOf
      rw [smul_smul, mul_one_div_cancel hln, one_smul]
    have := congrArg (fun y => ⟪w, y⟫_ℝ) h1
    simp only [inner_smul_right, inner_sum] at this
    rw [← this, real_inner_self_eq_norm_sq]
  have hgap : primal lam x φ w - (dual lam x φ α).toReal =
      1 / (n : ℝ) * ∑ i, (φ i ⟪w, x i⟫_ℝ + c i + α i * ⟪w, x i⟫_ℝ) := by
    rw [hD0r]
    unfold primal
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hinner, Finset.sum_neg_distrib]
    field_simp
    ring
  -- the one-coordinate analysis
  have hstep : ∀ i, ∃ c' : ℝ,
      dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i) =
        ((1 / (n : ℝ) * (∑ j, (-c j) + c i - c') -
          lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2 : ℝ) : EReal) ∧
      s * (φ i ⟪w, x i⟫_ℝ + c i + (α i * ⟪w, x i⟫_ℝ +
          (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u i ⟪w, x i⟫_ℝ - α i) ^ 2)) ≤
        (-c' - lam * n / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2) -
          (-c i - lam * n / 2 * ‖w‖ ^ 2) := by
    intro i
    have h10 := sds_eq10 hn x φ hconv lam hlam Δ hΔ α i (hfeas i) γ hγ (hsc i)
      (u i ⟪w, x i⟫_ℝ) (hu i ⟪w, x i⟫_ℝ) s ⟨hs0.le, hs1⟩
    rw [← hw] at h10
    set δ := Δ α i with hδ
    have hobj0 : coordObj lam x φ α i 0 = ((-c i - lam * n / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
      unfold coordObj
      simp only [add_zero, zero_smul, smul_zero]
      rw [hc i, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
    have hrhs : ((s : ℝ) : EReal) *
        (((φ i ⟪w, x i⟫_ℝ : ℝ) : EReal) + SDCA.Lipschitz.conj (φ i) (-α i) +
          ((α i * ⟪w, x i⟫_ℝ + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) *
            (u i ⟪w, x i⟫_ℝ - α i) ^ 2 : ℝ) : EReal)) =
        ((s * (φ i ⟪w, x i⟫_ℝ + c i + (α i * ⟪w, x i⟫_ℝ +
          (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u i ⟪w, x i⟫_ℝ - α i) ^ 2)) : ℝ)
          : EReal) := by
      rw [hc i, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul]
    rw [hrhs, hobj0] at h10
    have hne_top : SDCA.Lipschitz.conj (φ i) (-(α i + δ)) ≠ ⊤ := by
      intro htop
      have : coordObj lam x φ α i δ = ⊥ := by
        unfold coordObj
        rw [htop]
        simp
      rw [this] at h10
      have hb : (⊥ : EReal) - ((-c i - lam * n / 2 * ‖w‖ ^ 2 : ℝ) : EReal) = ⊥ := by simp
      rw [hb] at h10
      exact EReal.coe_ne_bot _ (le_bot_iff.mp h10)
    obtain ⟨c', hc'⟩ : ∃ c' : ℝ, SDCA.Lipschitz.conj (φ i) (-(α i + δ)) = (c' : EReal) := by
      lift SDCA.Lipschitz.conj (φ i) (-(α i + δ)) to ℝ using ⟨hne_top, sds_conj_ne_bot _ _⟩ with c' hc'
      exact ⟨c', rfl⟩
    have hobjδ : coordObj lam x φ α i δ =
        ((-c' - lam * n / 2 * ‖w + (lam * n)⁻¹ • (δ • x i)‖ ^ 2 : ℝ) : EReal) := by
      unfold coordObj
      rw [hc', ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
    rw [hobjδ, ← EReal.coe_sub, ge_iff_le, EReal.coe_le_coe_iff] at h10
    refine ⟨c', ?_, h10⟩
    -- the new dual value
    have hupd : SDCA.Lipschitz.sdcaStep Δ α i = α + Pi.single i δ := rfl
    have hw' : wOf lam x (SDCA.Lipschitz.sdcaStep Δ α i) = w + (lam * n)⁻¹ • (δ • x i) := by
      rw [hupd, hw]
      unfold wOf
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      have : ∑ j, (Pi.single i δ : Fin n → ℝ) j • x j = δ • x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_apply, hj]
        · simp
      rw [this, smul_add]
      simp only [one_div]
    set c'' : Fin n → ℝ := fun j => c j + if j = i then c' - c i else 0 with hc''
    have hcc : ∀ j, SDCA.Lipschitz.conj (φ j) (-(SDCA.Lipschitz.sdcaStep Δ α i) j) = (c'' j : EReal) := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [hupd, Pi.add_apply, Pi.single_eq_same, hc'', if_true]
        rw [hc']
        congr 1; ring
      · simp only [hupd, Pi.add_apply, Pi.single_eq_of_ne hji, add_zero, hc'', hji, if_false]
        rw [hc j]
    have hsum'' : ∑ j, (-c'' j) = ∑ j, (-c j) + c i - c' := by
      simp only [hc'', neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_ite_eq' Finset.univ i (fun _ => c' - c i)]
      simp
      ring
    unfold dual
    rw [hw']
    have hsE : ∑ j, -SDCA.Lipschitz.conj (φ j) (-(SDCA.Lipschitz.sdcaStep Δ α i) j) =
        ((∑ j, (-c'' j) : ℝ) : EReal) := by
      simp only [hcc]
      rw [sds_coe_esum]
      simp only [EReal.coe_neg]
    rw [hsE, hsum'', ← EReal.coe_mul, ← EReal.coe_sub]
  choose cc hcc using hstep
  refine ⟨fun i => by rw [(hcc i).1]; exact EReal.coe_ne_bot _, ?_⟩
  have hdr : ∀ i, (dual lam x φ (SDCA.Lipschitz.sdcaStep Δ α i)).toReal =
      1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2 := fun i => by rw [(hcc i).1]; rfl
  simp only [hdr]
  have hdiff : ∀ i, 1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2 - (dual lam x φ α).toReal ≥
      s * (φ i ⟪w, x i⟫_ℝ + c i + (α i * ⟪w, x i⟫_ℝ +
          (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u i ⟪w, x i⟫_ℝ - α i) ^ 2)) / n := by
    intro i
    have h2 := (hcc i).2
    have hE : 1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2 - (dual lam x φ α).toReal =
        ((-cc i - lam * n / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2) -
          (-c i - lam * n / 2 * ‖w‖ ^ 2)) / n := by
      rw [hD0r]
      field_simp
      ring
    rw [hE, ge_iff_le]
    exact div_le_div_of_nonneg_right h2 hnpos.le
  have hsum1 : 1 / (n : ℝ) * ∑ i, (1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2) - (dual lam x φ α).toReal =
      1 / (n : ℝ) * ∑ i, ((1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2) - (dual lam x φ α).toReal) := by
    rw [Finset.sum_sub_distrib (f := fun i => 1 / (n : ℝ) * (∑ j, (-c j) + c i - cc i) -
        lam / 2 * ‖w + (lam * n)⁻¹ • (Δ α i • x i)‖ ^ 2)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum1, ge_iff_le]
  have hRHS : s / n * (primal lam x φ w - (dual lam x φ α).toReal) -
      (s / n) ^ 2 * ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s) *
            (u i ⟪w, x i⟫_ℝ - α i) ^ 2) / (2 * lam) =
      1 / (n : ℝ) * ∑ i, (s * (φ i ⟪w, x i⟫_ℝ + c i + (α i * ⟪w, x i⟫_ℝ +
          (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u i ⟪w, x i⟫_ℝ - α i) ^ 2)) / n) := by
    rw [hgap]
    have e1 : (s / n) ^ 2 * ((1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s) *
            (u i ⟪w, x i⟫_ℝ - α i) ^ 2) / (2 * lam) =
        ∑ i, ((s / n) ^ 2 * ((1 / (n : ℝ)) * ((‖x i‖ ^ 2 - γ * (1 - s) * lam * n / s) *
            (u i ⟪w, x i⟫_ℝ - α i) ^ 2)) / (2 * lam)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    have e2 : s / n * (1 / (n : ℝ) * ∑ i, (φ i ⟪w, x i⟫_ℝ + c i + α i * ⟪w, x i⟫_ℝ)) =
        ∑ i, (s / n * (1 / (n : ℝ) * (φ i ⟪w, x i⟫_ℝ + c i + α i * ⟪w, x i⟫_ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  rw [hRHS]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun i _ => hdiff i)
