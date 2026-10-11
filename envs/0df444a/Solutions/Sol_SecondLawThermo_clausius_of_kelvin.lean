-- Prove2me | solution 1 for SecondLawThermo.clausius_of_kelvin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:32:34.28938+00:00
-- url     : https://prove2.me/submissions/b539d965-9e43-411b-9d17-683a00e7cc28

import Definitions.Def_SecondLawThermo_Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

private theorem work_two_reservoirs {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (h k : Θ) (hkh : k < h)
    (hbetween : OperatesBetween c h k) :
    work c = c h + c k := by
  classical
  have hne : h ≠ k := ne_of_gt hkh
  have hc : c = Finsupp.single h (c h) + Finsupp.single k (c k) := by
    ext t
    by_cases hth : t = h
    · subst t
      simp [hne]
    · by_cases htk : t = k
      · subst t
        simp [hne]
      · simp [hth, htk, hbetween t hth htk]
  rw [hc]
  simp [work, Finsupp.sum_single_add_single, ne_of_gt hkh]

theorem solution {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (SecondLawThermo.Cycle Θ)) (h𝒞 : IsCycleCone 𝒞)
    (hCarnot : CarnotEnginesExist 𝒞) (hK : KelvinStatement 𝒞) :
    ClausiusStatement 𝒞 := by
  classical
  unfold ClausiusStatement
  intro h k hkh c hc hbetween hw
  by_contra hn
  have hck : 0 < c k := lt_of_not_ge hn
  have hcwork : work c = c h + c k := work_two_reservoirs c h k hkh hbetween
  rw [hcwork] at hw
  have hch : c h = -c k := by linarith
  obtain ⟨e, he⟩ := hCarnot h k hkh
  rcases he with ⟨hrev, hebetween, hehot, hecold, hework⟩
  rcases hrev with ⟨hemem, hnegmem⟩
  have hB : 0 < -e k := neg_pos.mpr hecold
  have hwe : work e = e h + e k := work_two_reservoirs e h k hkh hebetween
  have hAB : 0 < e h + e k := by
    rw [← hwe]
    exact hework
  let scale : ℝ := c k / (-e k)
  have hscale : 0 < scale := div_pos hck hB
  have hscaleB : scale * (-e k) = c k := by
    dsimp [scale]
    exact div_mul_cancel₀ _ (ne_of_gt hB)
  let d : SecondLawThermo.Cycle Θ := c + scale • e
  have hdmem : d ∈ 𝒞 :=
    h𝒞.add_mem c (scale • e) hc (h𝒞.smul_mem scale e hscale.le hemem)
  have hdbetween : OperatesBetween d h k := by
    intro t hth htk
    simp [d, hbetween t hth htk, hebetween t hth htk]
  have hdk : d k = 0 := by
    simp only [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      c k + scale * e k = c k - scale * (-e k) := by ring
      _ = 0 := by rw [hscaleB]; ring
  have hdh : d h = c h + scale * e h := by
    simp [d]
  have hdhpos : 0 < d h := by
    rw [hdh, hch]
    have hprod : 0 < scale * (e h + e k) := mul_pos hscale hAB
    nlinarith [hscaleB, hprod]
  have honly : ∀ s, s ≠ h → d s = 0 := by
    intro s hsh
    by_cases hsk : s = k
    · subst s
      exact hdk
    · exact hdbetween s hsh hsk
  have hdwork : work d = d h + d k := work_two_reservoirs d h k hkh hdbetween
  have hdworkpos : 0 < work d := by
    rw [hdwork, hdk]
    simpa using hdhpos
  have := hK h d hdmem honly
  linarith
