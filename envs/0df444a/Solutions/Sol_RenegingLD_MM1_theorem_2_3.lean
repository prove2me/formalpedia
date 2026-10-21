-- Prove2me | solution 1 for RenegingLD.MM1.theorem_2_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:41:23.506811+00:00
-- url     : https://prove2.me/submissions/d1b4edd4-5a31-40af-a9a9-fe5c3184bc60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational
import Theorems.Thm_RenegingLD_MM1_proposition_6_2
import Theorems.Thm_RenegingLD_MM1_proposition_6_3
import Theorems.Thm_RenegingLD_MM1_proposition_6_4
import Theorems.Thm_RenegingLD_MM1_lemma_6_1
import Theorems.Thm_RenegingLD_MM1_eq_6_1_C_cont

open RenegingLD.MM1
open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 : ℝ) (hx0 : 0 ≤ x0) :
    (∀ γ : ℝ, 0 ≤ γ →
      Tendsto (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) ∧
    (∀ γ : ℝ, lam - mu ≤ γ →
      Tendsto (fun T => Iup lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) ∧
    (∀ γ : ℝ, 0 ≤ γ → γ ≤ lam - mu →
      Tendsto (fun T => Idown lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) := by
  -- Part 1: the limit of I*_{γ,T}/T.
  have hstar : ∀ γ : ℝ, 0 ≤ γ →
      Tendsto (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ))) := by
    intro γ hγ
    have hsup := proposition_6_2 lam mu θ hlam hmu hθ hlm x0 γ hx0 hγ
    have hinf : ENNReal.ofReal (C lam mu γ) ≤
        Filter.liminf (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop := by
      rcases hγ.lt_or_eq with h | h
      · exact proposition_6_3 lam mu θ hlam hmu hθ hlm x0 γ hx0 h
      · subst h; exact proposition_6_4 lam mu θ hlam hmu hθ hlm x0 hx0
    exact tendsto_of_le_liminf_of_limsup_le hinf hsup
  -- γ*_T → λ − µ
  have hexp : Tendsto (fun T : ℝ => Real.exp (-θ * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hgs : Tendsto (fun T => gammaStar lam mu θ x0 T) atTop (𝓝 (lam - mu)) := by
    have h1 : Tendsto (fun T : ℝ => (1 - Real.exp (-θ * T)) * T⁻¹ * (x0 - (lam - mu) / θ))
        atTop (𝓝 ((1 - 0) * 0 * (x0 - (lam - mu) / θ))) :=
      ((tendsto_const_nhds.sub hexp).mul tendsto_inv_atTop_zero).mul tendsto_const_nhds
    simp only [sub_zero, mul_zero, zero_mul] at h1
    have h2 := (tendsto_const_nhds (x := lam - mu)).add h1
    simp only [add_zero] at h2
    refine h2.congr fun T => ?_
    simp [gammaStar, div_eq_mul_inv]
  -- trivial comparisons
  have up_le : ∀ γ T, Iup lam mu θ x0 γ T ≤ Istar lam mu θ x0 γ T := by
    intro γ T
    refine le_iInf fun ξ => le_iInf fun ζ => le_iInf fun h => ?_
    exact iInf_le_of_le ξ (iInf_le_of_le ζ (iInf_le_of_le h.ge le_rfl))
  have down_le : ∀ γ T, Idown lam mu θ x0 γ T ≤ Istar lam mu θ x0 γ T := by
    intro γ T
    refine le_iInf fun ξ => le_iInf fun ζ => le_iInf fun h => ?_
    exact iInf_le_of_le ξ (iInf_le_of_le ζ (iInf_le_of_le h.le le_rfl))
  -- I_{γ,T} = I*_{γ,T} when γ ≥ γ*_T
  have up_eq : ∀ γ T, 0 < T → gammaStar lam mu θ x0 T ≤ γ →
      Iup lam mu θ x0 γ T = Istar lam mu θ x0 γ T := by
    intro γ T hT hg
    refine le_antisymm (up_le γ T) ?_
    have hmono := (lemma_6_1 lam mu θ hlam hmu hθ hlm x0 T hx0 hT).2.2.2
    refine le_iInf fun ξ => le_iInf fun ζ => le_iInf fun h => ?_
    set γ' := ζ T / T
    have hζ : ζ T = γ' * T := by simp only [γ']; field_simp
    have hγγ' : γ ≤ γ' := by
      simp only [γ']; rw [le_div_iff₀ hT]; exact h
    calc Istar lam mu θ x0 γ T ≤ Istar lam mu θ x0 γ' T :=
          hmono (Set.mem_Ici.2 hg) (Set.mem_Ici.2 (hg.trans hγγ')) hγγ'
      _ ≤ IT lam mu θ x0 T ξ ζ := iInf_le_of_le ξ (iInf_le_of_le ζ (iInf_le_of_le hζ le_rfl))
  -- Ĩ_{γ,T} = I*_{γ,T} when 0 ≤ γ ≤ γ*_T
  have down_eq : ∀ γ T, 0 < T → 0 ≤ γ → γ ≤ gammaStar lam mu θ x0 T →
      Idown lam mu θ x0 γ T = Istar lam mu θ x0 γ T := by
    intro γ T hT hγ0 hg
    refine le_antisymm (down_le γ T) ?_
    have hanti := (lemma_6_1 lam mu θ hlam hmu hθ hlm x0 T hx0 hT).2.2.1
    refine le_iInf fun ξ => le_iInf fun ζ => le_iInf fun h => ?_
    by_cases hneg : ζ T < 0
    · have hnp : ¬ IsPath T ξ ζ := by
        intro hp
        have := (hp.2.2 T ⟨hT.le, le_rfl⟩).2
        linarith
      have : IT lam mu θ x0 T ξ ζ = ⊤ := by
        simp [IT, hnp]
      rw [this]; exact le_top
    · push Not at hneg
      set γ' := ζ T / T
      have hζ : ζ T = γ' * T := by simp only [γ']; field_simp
      have hγ'γ : γ' ≤ γ := by
        simp only [γ']; rw [div_le_iff₀ hT]; exact h
      have hγ'0 : 0 ≤ γ' := div_nonneg hneg hT.le
      calc Istar lam mu θ x0 γ T ≤ Istar lam mu θ x0 γ' T :=
            hanti ⟨hγ'0, hγ'γ.trans hg⟩ ⟨hγ0, hg⟩ hγ'γ
        _ ≤ IT lam mu θ x0 T ξ ζ := iInf_le_of_le ξ (iInf_le_of_le ζ (iInf_le_of_le hζ le_rfl))
  have hC0 : C lam mu (lam - mu) = 0 := (eq_6_1_C_cont lam mu hlam hmu hlm).2.2
  have hlm0 : 0 ≤ lam - mu := by linarith
  -- boundary case γ = λ − µ: squeeze between 0 and I*/T
  have squeeze : ∀ f : ℝ → ℝ≥0∞, (∀ T, f T ≤ Istar lam mu θ x0 (lam - mu) T) →
      Tendsto (fun T => f T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu (lam - mu)))) := by
    intro f hf
    have h := hstar (lam - mu) hlm0
    rw [hC0, ENNReal.ofReal_zero] at h ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) (fun T => ENNReal.div_le_div_right (hf T) _)
  refine ⟨hstar, ?_, ?_⟩
  · intro γ hγ
    rcases hγ.lt_or_eq with h | h
    · have hev : ∀ᶠ T in atTop, gammaStar lam mu θ x0 T < γ := (tendsto_order.1 hgs).2 γ h
      refine (hstar γ (hlm0.trans hγ)).congr' ?_
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with T h1 h2
      rw [up_eq γ T h2 h1.le]
    · subst h
      exact squeeze _ (up_le _)
  · intro γ hγ0 hγ
    rcases hγ.lt_or_eq with h | h
    · have hev : ∀ᶠ T in atTop, γ < gammaStar lam mu θ x0 T := (tendsto_order.1 hgs).1 γ h
      refine (hstar γ hγ0).congr' ?_
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with T h1 h2
      rw [down_eq γ T h2 hγ0 h1.le]
    · subst h
      exact squeeze _ (down_le _)
