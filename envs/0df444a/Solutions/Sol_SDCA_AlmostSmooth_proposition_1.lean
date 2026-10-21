-- Prove2me | solution 1 for SDCA.AlmostSmooth.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:51:23.114989+00:00
-- url     : https://prove2.me/submissions/56e89f27-998d-4ecc-8ff6-72baccd68f6c

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

set_option autoImplicit false
open scoped InnerProductSpace
open SDCA.AlmostSmooth
open SDCA.Lipschitz (conj)

theorem sda_conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

theorem sda_conj_real (ψ : ℝ → ℝ) (u : ℝ) (h : conj ψ u ≠ ⊤) : ∃ c : ℝ, conj ψ u = (c : EReal) := by
  lift conj ψ u to ℝ using ⟨h, sda_conj_ne_bot ψ u⟩ with c hc
  exact ⟨c, rfl⟩

theorem sda_conj_subgrad (ψ : ℝ → ℝ) (a g : ℝ) (h : ∀ z : ℝ, ψ a + g * (z - a) ≤ ψ z) :
    conj ψ g = ((a * g - ψ a : ℝ) : EReal) := by
  apply le_antisymm
  · unfold conj
    refine iSup_le (fun z => ?_)
    rw [EReal.coe_le_coe_iff]
    have := h z
    linarith
  · exact le_iSup (fun z : ℝ => ((z * g - ψ z : ℝ) : EReal)) a

theorem sda_coe_esum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  let g : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  exact map_sum g _ _

/-- a subgradient of `φ` at `p` with slope `-a` gives a subgradient of `φ*` at `-a`. -/
theorem sda_conj_subgrad_isConj (ψ : ℝ → ℝ) (p a : ℝ) (h : IsSubgrad ψ p (-a)) :
    IsConjSubgrad ψ (-a) p := by
  have hc : conj ψ (-a) = ((p * (-a) - ψ p : ℝ) : EReal) := sda_conj_subgrad ψ p (-a) h
  refine ⟨by rw [hc]; exact EReal.coe_ne_top _, fun v' => ?_⟩
  rw [hc, ← EReal.coe_add]
  refine le_trans ?_ (le_iSup (fun z : ℝ => ((z * v' - ψ z : ℝ) : EReal)) p)
  rw [EReal.coe_le_coe_iff]
  linarith

theorem sda_dual_real {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (lam : ℝ) (α : Fin n → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, conj (φ i) (-α i) = (c i : EReal)) :
    SDCA.Smooth.dual lam x φ α =
      ((1 / (n : ℝ) * ∑ i, (-c i) - lam / 2 * ‖SDCA.Smooth.wOf lam x α‖ ^ 2 : ℝ) : EReal) := by
  unfold SDCA.Smooth.dual
  simp only [hc]
  simp only [EReal.coe_sub, EReal.coe_mul, sda_coe_esum, EReal.coe_neg]

theorem sda_sum_x {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hn : 0 < n)
    (hlam : 0 < lam) (β : Fin n → ℝ) :
    ∑ i, β i • x i = (lam * n) • SDCA.Smooth.wOf lam x β := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  unfold SDCA.Smooth.wOf
  rw [smul_smul, mul_one_div_cancel hln, one_smul]

theorem solution {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (γfun : Fin n → ℝ → ℝ)
    (h4 : RefinedDualStrongConvexity φ γfun) (αstar : Fin n → ℝ)
    (hstar : ∀ i, IsSubgrad (φ i) ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ (-αstar i)) :
    DualStrongConvexity lam x φ (fun i => γfun i ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ) αstar ∧
      ∀ (w : EuclideanSpace ℝ (Fin d)) (i : Fin n) (a : ℝ), IsSubgrad (φ i) ⟪w, x i⟫_ℝ (-a) →
        γfun i ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ * |a - αstar i| ≤
          |⟪SDCA.Smooth.wOf lam x αstar - w, x i⟫_ℝ| := by
  obtain ⟨hγ0, h4⟩ := h4
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set ws := SDCA.Smooth.wOf lam x αstar with hws
  have hcs : ∀ i, conj (φ i) (-αstar i) = ((⟪ws, x i⟫_ℝ * (-αstar i) - φ i ⟪ws, x i⟫_ℝ : ℝ) : EReal) :=
    fun i => sda_conj_subgrad _ _ _ (hstar i)
  have hCS : ∀ i, IsConjSubgrad (φ i) (-αstar i) ⟪ws, x i⟫_ℝ :=
    fun i => sda_conj_subgrad_isConj _ _ _ (hstar i)
  constructor
  · intro α hα
    choose c hc using (fun i => sda_conj_real (φ i) (-α i) (hα i))
    set cs : Fin n → ℝ := fun i => ⟪ws, x i⟫_ℝ * (-αstar i) - φ i ⟪ws, x i⟫_ℝ with hcsdef
    have hcs' : ∀ i, conj (φ i) (-αstar i) = (cs i : EReal) := hcs
    have h4i : ∀ i, γfun i ⟪ws, x i⟫_ℝ * |α i - αstar i| ^ 2 ≤
        c i - cs i + ⟪ws, x i⟫_ℝ * (α i - αstar i) := by
      intro i
      have := h4 i (α i) (αstar i) ⟪ws, x i⟫_ℝ (hCS i)
      rw [hc i, hcs' i, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    have hmain : ∑ i, γfun i ⟪ws, x i⟫_ℝ * |α i - αstar i| ^ 2 ≤
        ∑ i, c i - ∑ i, cs i + ∑ i, ⟪ws, x i⟫_ℝ * (α i - αstar i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => h4i i)
    set w := SDCA.Smooth.wOf lam x α with hw
    have hlin : ∑ i, ⟪ws, x i⟫_ℝ * (α i - αstar i) = lam * n * (⟪ws, w⟫_ℝ - ‖ws‖ ^ 2) := by
      have h1 : ∑ i, (α i - αstar i) • x i = (lam * n) • (w - ws) := by
        have e1 := sda_sum_x x lam hn hlam α
        have e2 := sda_sum_x x lam hn hlam αstar
        simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, smul_sub]
        rw [hw, hws]
      have := congrArg (fun y => ⟪ws, y⟫_ℝ) h1
      simp only [inner_smul_right, inner_sum, inner_sub_right] at this
      rw [real_inner_self_eq_norm_sq] at this
      rw [← mul_comm] at this
      have e3 : ∑ i, ⟪ws, x i⟫_ℝ * (α i - αstar i) = ∑ i, (α i - αstar i) * ⟪ws, x i⟫_ℝ :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [e3, this]; ring
    rw [sda_dual_real x φ lam αstar cs hcs', sda_dual_real x φ lam α c hc, ← hws, ← hw,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h5 : 1 / (n : ℝ) * ∑ i, γfun i ⟪ws, x i⟫_ℝ * |α i - αstar i| ^ 2 ≤
        1 / (n : ℝ) * (∑ i, c i - ∑ i, cs i + lam * n * (⟪ws, w⟫_ℝ - ‖ws‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hlin]; exact hmain
    have h6 : 1 / (n : ℝ) * (∑ i, c i - ∑ i, cs i + lam * n * (⟪ws, w⟫_ℝ - ‖ws‖ ^ 2)) =
        1 / (n : ℝ) * ∑ i, c i - 1 / (n : ℝ) * ∑ i, cs i + lam * (⟪ws, w⟫_ℝ - ‖ws‖ ^ 2) := by
      field_simp
    have h7 : ‖w - ws‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪ws, w⟫_ℝ + ‖ws‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm]
    rw [h7]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    simp only [Finset.sum_neg_distrib] at *
    nlinarith [h5, h6]
  · intro w i a ha
    have hCa := sda_conj_subgrad_isConj _ _ _ ha
    have hca : conj (φ i) (-a) = ((⟪w, x i⟫_ℝ * (-a) - φ i ⟪w, x i⟫_ℝ : ℝ) : EReal) :=
      sda_conj_subgrad _ _ _ ha
    -- (4) at (a, αstar i) with u = ws·x_i
    have e1 := h4 i a (αstar i) ⟪ws, x i⟫_ℝ (hCS i)
    rw [hca, hcs i, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff] at e1
    -- (4) at (αstar i, a) with u = w·x_i : only nonnegativity of γ is used
    have e2 := h4 i (αstar i) a ⟪w, x i⟫_ℝ hCa
    rw [hca, hcs i, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff] at e2
    have e3 := mul_nonneg (hγ0 i ⟪w, x i⟫_ℝ) (sq_nonneg |αstar i - a|)
    have hgi := hγ0 i ⟪ws, x i⟫_ℝ
    set g := γfun i ⟪ws, x i⟫_ℝ
    have hsq : g * |a - αstar i| ^ 2 ≤ (⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ) * (a - αstar i) := by
      nlinarith
    have hin : ⟪ws - w, x i⟫_ℝ = ⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ := inner_sub_left _ _ _
    rw [hin]
    set δ := |a - αstar i| with hδ
    have hδ0 : 0 ≤ δ := abs_nonneg _
    have hle : g * δ ^ 2 ≤ |⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ| * δ := by
      refine hsq.trans ?_
      calc (⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ) * (a - αstar i)
          ≤ |(⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ) * (a - αstar i)| := le_abs_self _
        _ = |⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ| * δ := by rw [abs_mul]
    rcases hδ0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have : g * δ * δ ≤ |⟪ws, x i⟫_ℝ - ⟪w, x i⟫_ℝ| * δ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
