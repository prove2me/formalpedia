-- Prove2me | solution 1 for WassDDRO.Consistency.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T12:07:37.662087+00:00
-- url     : https://prove2.me/submissions/6628cac3-e0b4-4493-bad2-e7f36a7db76a

import Definitions.Def_WassDDRO_Consistency_Setting
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassConsistencyCodex

noncomputable def upperEnvelope {E : Type*} [NormedAddCommGroup E] (Ξ : Set E) (h : E → ℝ)
    (lam : ℝ) (x : E) : ℝ := sSup ((fun y => h y-lam*‖y-x‖) '' Ξ)

theorem envelope_point_bound {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x y : E) (hy : y∈Ξ) :
    h y-lam*‖y-x‖ ≤ L*(1+‖x‖) := by
  have hn : ‖y‖ ≤ ‖y-x‖+‖x‖ := by
    calc
      _ = ‖(y-x)+x‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hm := mul_le_mul_of_nonneg_left hn hL
  have hp := mul_le_mul_of_nonneg_right hlam (norm_nonneg (y-x))
  nlinarith [hg y hy]

theorem envelope_bddAbove {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) :
    BddAbove ((fun y => h y-lam*‖y-x‖) '' Ξ) := by
  refine ⟨L*(1+‖x‖),?_⟩
  rintro r ⟨y,hy,rfl⟩
  exact envelope_point_bound Ξ h L lam hL hlam hg x y hy

theorem upperEnvelope_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) : upperEnvelope Ξ h lam x ≤ L*(1+‖x‖) := by
  apply csSup_le (hne.image _)
  rintro r ⟨y,hy,rfl⟩
  exact envelope_point_bound Ξ h L lam hL hlam hg x y hy

theorem le_upperEnvelope_on {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) : h x ≤ upperEnvelope Ξ h lam x := by
  apply le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg x)
  exact ⟨x,hx,by simp⟩
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex

theorem upperEnvelope_le_add {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) (x y : E) :
    upperEnvelope Ξ h lam x ≤ upperEnvelope Ξ h lam y+lam*‖x-y‖ := by
  apply csSup_le (hne.image _)
  rintro r ⟨z,hz,rfl⟩
  have hd : ‖z-y‖ ≤ ‖z-x‖+‖x-y‖ := by
    have he : z-y=(z-x)+(x-y) := by abel
    rw [he]
    exact norm_add_le _ _
  have hm := mul_le_mul_of_nonneg_left hd (hL.trans hlam)
  have hy : h z-lam*‖z-y‖ ≤ upperEnvelope Ξ h lam y :=
    le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg y) ⟨z,hz,rfl⟩
  linarith

theorem upperEnvelope_lipschitz {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam : ℝ) (hL : 0 ≤ L) (hlam : L ≤ lam)
    (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) :
    LipschitzWith (Real.toNNReal lam) (upperEnvelope Ξ h lam) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal lam (hL.trans hlam),Real.dist_eq,dist_eq_norm,abs_le]
  constructor
  · have hm := upperEnvelope_le_add Ξ hne h L lam hL hlam hg y x
    rw [norm_sub_rev y x] at hm
    linarith
  · have hm := upperEnvelope_le_add Ξ hne h L lam hL hlam hg x y
    linarith

theorem upperEnvelope_antitone_penalty {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L lam mu : ℝ) (hL : 0 ≤ L)
    (hlam : L ≤ lam) (hmu : lam ≤ mu) (hg : ∀ z∈Ξ, h z ≤ L*(1+‖z‖)) (x : E) :
    upperEnvelope Ξ h mu x ≤ upperEnvelope Ξ h lam x := by
  apply csSup_le (hne.image _)
  rintro r ⟨z,hz,rfl⟩
  have hp := mul_le_mul_of_nonneg_right hmu (norm_nonneg (z-x))
  have hm : h z-lam*‖z-x‖ ≤ upperEnvelope Ξ h lam x :=
    le_csSup (envelope_bddAbove Ξ h L lam hL hlam hg x) ⟨z,hz,rfl⟩
  linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassConsistencyCodex

theorem upperEnvelope_eventual_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ lam0 : ℝ, L ≤ lam0 ∧ ∀ lam : ℝ, lam0 ≤ lam → upperEnvelope Ξ h lam x ≤ h x+δ := by
  have hn : ∀ᶠ y in 𝓝[Ξ] x, h y < h x+δ := (husc x hx) _ (by linarith)
  obtain ⟨ρ,hρ,hlocal⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let C : ℝ := L*(1+‖x‖)
  let w : ℝ := max 0 ((C-(h x+δ))/ρ)
  have hw : 0 ≤ w := le_max_left _ _
  have hwr : C-(h x+δ) ≤ w*ρ := (div_le_iff₀ hρ).mp (le_max_right _ _)
  refine ⟨L+w,by linarith,?_⟩
  intro lam hlam0
  have hlam : L ≤ lam := by linarith
  have hlam0' : 0 ≤ lam := hL.trans hlam
  have hdiff : w ≤ lam-L := by linarith
  have hdiff0 : 0 ≤ lam-L := sub_nonneg.mpr hlam
  apply csSup_le ((show Ξ.Nonempty from ⟨x,hx⟩).image _)
  rintro r ⟨y,hy,rfl⟩
  by_cases hd : ‖y-x‖ < ρ
  · have hh : h y < h x+δ := hlocal ⟨by simpa [Metric.mem_ball,dist_eq_norm] using hd,hy⟩
    have hp : 0 ≤ lam*‖y-x‖ := mul_nonneg hlam0' (norm_nonneg _)
    linarith
  · have hdist : ρ ≤ ‖y-x‖ := le_of_not_gt hd
    have hp : w*ρ ≤ (lam-L)*‖y-x‖ :=
      (mul_le_mul_of_nonneg_right hdiff hρ.le).trans (mul_le_mul_of_nonneg_left hdist hdiff0)
    have hh := envelope_point_bound Ξ h L L hL le_rfl hg x y hy
    change h y-L*‖y-x‖ ≤ C at hh
    calc
      _ = (h y-L*‖y-x‖)-(lam-L)*‖y-x‖ := by ring
      _ ≤ C-(lam-L)*‖y-x‖ := sub_le_sub_right hh _
      _ ≤ _ := by linarith
end WassConsistencyCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassConsistencyCodex

theorem upperEnvelope_nat_tendsto {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (x : E) (hx : x∈Ξ) :
    Tendsto (fun k : ℕ => upperEnvelope Ξ h (L+(k : ℝ)+1) x) atTop (𝓝 (h x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨lam0,hL0,hupper⟩ := upperEnvelope_eventual_upper Ξ h husc L hL hg x hx (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_ge lam0
  refine ⟨N,?_⟩
  intro k hk
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlam : lam0 ≤ L+(k : ℝ)+1 := by linarith
  have hΓ : L ≤ L+(k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlo := le_upperEnvelope_on Ξ h L (L+(k : ℝ)+1) hL hΓ hg x hx
  have hup := hupper (L+(k : ℝ)+1) hlam
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem upperEnvelope_nat_antitone {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (hne : Ξ.Nonempty) (h : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ y∈Ξ, h y ≤ L*(1+‖y‖)) (k : ℕ) (x : E) :
    upperEnvelope Ξ h (L+((k+1 : ℕ) : ℝ)+1) x ≤ upperEnvelope Ξ h (L+(k : ℝ)+1) x := by
  apply upperEnvelope_antitone_penalty Ξ hne h L _ _ hL _ _ hg x
  · linarith [Nat.cast_nonneg (α := ℝ) k]
  · push_cast
    linarith
end WassConsistencyCodex

end

set_option autoImplicit false
open Filter Topology
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hgrowth : ∀ ξ ∈ Ξ, h ξ ≤ L * (1 + ‖ξ‖)) :
    ∃ hk : ℕ → E → ℝ, (∀ k, ∃ Lk : NNReal, LipschitzOnWith Lk (hk k) Ξ) ∧
      (∀ k, ∀ ξ ∈ Ξ, hk (k + 1) ξ ≤ hk k ξ) ∧
      ∀ ξ ∈ Ξ, Tendsto (fun k => hk k ξ) atTop (𝓝 (h ξ)) := by
  classical
  rcases Ξ.eq_empty_or_nonempty with hempty | hne
  · subst Ξ
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro k
      exact ⟨0, by simp [LipschitzOnWith]⟩
    · simp
    · simp
  · refine ⟨fun k => WassConsistencyCodex.upperEnvelope Ξ h (L+(k : ℝ)+1), ?_, ?_, ?_⟩
    · intro k
      refine ⟨Real.toNNReal (L+(k : ℝ)+1), ?_⟩
      exact (WassConsistencyCodex.upperEnvelope_lipschitz Ξ hne h L _ hL
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) hgrowth).lipschitzOnWith
    · intro k ξ hξ
      exact WassConsistencyCodex.upperEnvelope_nat_antitone Ξ hne h L hL hgrowth k ξ
    · intro ξ hξ
      exact WassConsistencyCodex.upperEnvelope_nat_tendsto Ξ h husc L hL hgrowth ξ hξ


#print axioms solution
