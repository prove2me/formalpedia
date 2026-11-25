-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.orth_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:33:17.232231+00:00
-- url     : https://prove2.me/submissions/b3ac3828-39c5-4c54-9181-5f59352ee40c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_cont_ip
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_l2Inner_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_pi_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_ip_U
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_ip_periodic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pullbackSection_mem_thetaSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_translate_pullbackSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private theorem continuous_of_mem_Sec (X : PT E) {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Continuous F :=
  hF.1.continuous
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (hT : StepT) (hDual : StepDual) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    {b b' : Fin n → Vsp X.dim} (hb : b ∈ K) (hb' : b' ∈ K) (hne : b ≠ b') :
    X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0 := by
  by_contra hI
  apply hne
  have hF0 : s0 X (n := n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs
  have hUb : X.U q b (s0 X π s) ∈ X.Sec q n := nA_U_mem (X := X) hF0 (hK.1 b hb)
  have hUb' : X.U q b' (s0 X π s) ∈ X.Sec q n := nA_U_mem (X := X) hF0 (hK.1 b' hb')

  have hinv : ∀ (k : Fin n → Vsp X.dim) {F G : (Fin n → Vsp X.dim) → ℂ}, F ∈ X.Sec q n →
      G ∈ X.Sec q n → X.l2ip q (X.U q k F) (X.U q k G) = X.l2ip q F G := by
    intro k F G hF hG
    have key := hT E X n ℂ
      (fun v => F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ))
      (cont_ip q (continuous_of_mem_Sec X hF) (continuous_of_mem_Sec X hG))
      (fun γ hγ v => nA_ip_periodic (X := X) hF hG hγ v) k
    unfold PT.l2ip
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact nA_ip_U (X := X) q k F G v
  have hUs0 : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) →
      X.U q k (s0 X π s) = fun v => (∏ j, (X.eps (π (k j)) : ℂ)) * s0 X π s v :=
    fun k hk => funext fun v => translate_pullbackSection (X := X) hπ hs hk v
  have hshift : ∀ (a k : Fin n → Vsp X.dim), (∀ j, π (k j) ∈ X.L) →
      X.U q k (X.U q a (s0 X π s)) =
        fun v => (cexp ((q : ℂ) * Real.pi * (HC a k - HC k a)) * ∏ j, (X.eps (π (k j)) : ℂ)) *
          X.U q a (s0 X π s) v := by
    intro a k hk
    funext v
    rw [nA_U_comm (X := X) q k a _ v, hUs0 k hk, nA_U_smul (X := X) q a _ (s0 X π s)]
    try dsimp only
    ring

  have hphase : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) →
      cexp ((q : ℂ) * Real.pi * (HC (b - b') k - HC k (b - b'))) = 1 := by
    intro k hk
    have hε2 : (∏ j, (X.eps (π (k j)) : ℂ)) * (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = 1 := by
      have c1 : (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = ∏ j, (X.eps (π (k j)) : ℂ) :=
        nA_epsprod_conj (X := X) (fun j => π (k j))
      have c2 : (∏ j, (X.eps (π (k j)) : ℂ)) ^ 2 = 1 :=
        nA_epsprod_sq (X := X) (γ := fun j => π (k j)) hk
      rw [c1, ← sq, c2]
    have h1 := hinv k hUb hUb'
    rw [hshift b k hk, hshift b' k hk, l2Inner_smul] at h1
    have hc := mul_right_cancel₀ hI (h1.trans (one_mul _).symm)
    have hw : (starRingEnd ℂ) ((q : ℂ) * Real.pi * (HC b' k - HC k b')) =
        (q : ℂ) * Real.pi * (HC k b' - HC b' k) := by
      rw [map_mul, map_mul, map_sub, nA_HC_conj, nA_HC_conj, map_natCast, Complex.conj_ofReal]
    rw [← hc, map_mul,
      show ∀ a e c f : ℂ, a * e * (c * f) = a * c * (e * f) from fun a e c f => by ring,
      hε2, mul_one, ← Complex.exp_conj, hw, ← Complex.exp_add, nA_HC_sub_left, nA_HC_sub_right]
    congr 1
    ring

  have hmem : ∀ j, π ((b - b') j) ∈ X.L := by
    intro j
    apply hDual E X (π ((b - b') j))
    intro y hy
    obtain ⟨z, rfl⟩ := (pi_bij X hq hπ).2 y
    have hk : ∀ i, π ((Pi.single j z : Fin n → Vsp X.dim) i) ∈ X.L := by
      intro i
      rcases eq_or_ne i j with rfl | h
      · rw [Pi.single_eq_same]; exact hy
      · rw [Pi.single_eq_of_ne h, map_zero]; exact X.L.zero_mem
    have hexp := hphase (Pi.single j z) hk
    have hHC : HC (b - b') (Pi.single j z) = Hf ((b - b') j) z := by
      unfold HC
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij]
        simp [Hf]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [← nA_HC_conj (b - b') (Pi.single j z), hHC] at hexp
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
    refine ⟨m, ?_⟩
    rw [Complex.sub_conj] at hm
    have key : (((q : ℝ) * (Hf ((b - b') j) z).im : ℝ) : ℂ) = (m : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      rw [← hm]
      push_cast
      ring
    have key' : (q : ℝ) * (Hf ((b - b') j) z).im = m := by exact_mod_cast key
    rw [hπ.2.2.1, ← key']
    simp [Complex.mul_im]
  exact (hK.2 b (hK.1 b hb)).unique
    ⟨hb, fun k => by rw [sub_self, map_zero]; exact X.L.zero_mem⟩ ⟨hb', fun k => hmem k⟩
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
