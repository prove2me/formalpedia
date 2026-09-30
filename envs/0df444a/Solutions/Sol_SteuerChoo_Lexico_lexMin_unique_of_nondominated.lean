-- Prove2me | solution 1 for SteuerChoo.Lexico.lexMin_unique_of_nondominated
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:15:58.307527+00:00
-- url     : https://prove2.me/submissions/dca6aa34-10c0-45d2-95b4-14281e164f36

import Definitions.Def_SteuerChoo_Lexico_IsIdealVector
import Definitions.Def_SteuerChoo_Lexico_lamBar
import Definitions.Def_SteuerChoo_Lexico_tcheb
import Definitions.Def_SteuerChoo_Lexico_Phi
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic
import Definitions.Def_SteuerChoo_Lexico_IsLexMin
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
set_option autoImplicit false
open Finset SteuerChoo.Lexico

private theorem ideal_upper {k : ℕ} (Z : Set (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (h : IsIdealVector Z zstar) (z : Fin k → ℝ) (hz : z∈Z) (i : Fin k) : z i ≤ zstar i := by
  obtain ⟨eps,heps,hmax,hpos⟩ := h
  obtain ⟨w,hw,he⟩ := hmax i
  have hh := hw.2 z hz
  rw [he]
  linarith [heps i]

private theorem zero_unique {k : ℕ} (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (hzbar : zbar∈nondominated Z)
    (j : Fin k) (hj : zbar j=zstar j) :
    (∀ z∈nondominated Z, z j=zstar j → z=zbar) ∧
      ∀ i, zbar i=zstar i → i=j := by
  obtain ⟨eps,heps,hmax,hpos⟩ := hideal
  have hu (z : Fin k → ℝ) (hz : z∈Z) (i : Fin k) : z i ≤ zstar i := by
    obtain ⟨w,hw,he⟩ := hmax i
    have hh := hw.2 z hz
    rw [he]
    linarith [heps i]
  obtain ⟨w,hw,he⟩ := hmax j
  have heps0 : eps j=0 := by
    have hh := hw.2 zbar hzbar.1
    linarith [heps j]
  have hbarmax : MaximizesObj Z j zbar := ⟨hzbar.1,fun z hz => by rw [hj]; exact hu z hz j⟩
  have hunique : ∀ z∈nondominated Z, z j=zstar j → z=zbar := by
    intro z hz hzj
    by_contra hne
    have hzm : MaximizesObj Z j z := ⟨hz.1,fun w hw => by rw [hzj]; exact hu w hw j⟩
    have hp := hpos j (Or.inl ⟨z,hz,zbar,hzbar,hne,hzm,hbarmax⟩)
    linarith
  refine ⟨hunique,?_⟩
  intro i hi
  by_contra hij
  have hbari : MaximizesObj Z i zbar := ⟨hzbar.1,fun z hz => by rw [hi]; exact hu z hz i⟩
  have hc : CondII Z j := by
    refine ⟨zbar,hzbar,hbarmax,?_,i,hij,hbari⟩
    intro z hz hzm
    apply hunique z hz
    have hh := hzm.2 zbar hzbar.1
    have huj := hu z hz.1 j
    linarith
  have hp := hpos j (Or.inr hc)
  linarith

private theorem nondom_eq_of_le {k : ℕ} (Z : Set (Fin k → ℝ)) (zbar : Fin k → ℝ)
    (hzbar : zbar∈nondominated Z) (w : Fin k → ℝ) (hw : w∈Z)
    (hle : ∀ i, zbar i≤w i) : w=zbar := by
  by_contra hne
  have hex : ∃ i, zbar i < w i := by
    by_contra hn
    push_neg at hn
    apply hne
    funext i
    exact le_antisymm (hn i) (hle i)
  exact hzbar.2 ⟨w,hw,hle,hex⟩

private theorem weight_model {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (hzbar : zbar∈nondominated Z) :
    lamBar zstar zbar∈stdSimplex ℝ (Fin k) ∧
    0 ≤ tcheb (lamBar zstar zbar) zstar zbar ∧
    (∀ w∈Z, tcheb (lamBar zstar zbar) zstar zbar ≤ tcheb (lamBar zstar zbar) zstar w) ∧
    (∀ w∈nondominated Z, tcheb (lamBar zstar zbar) zstar w ≤ tcheb (lamBar zstar zbar) zstar zbar → w=zbar) := by
  classical
  by_cases hz : ∀ i, zbar i≠zstar i
  · have hgap (i : Fin k) : 0 < zstar i-zbar i := by
      have hh := ideal_upper Z zstar hideal zbar hzbar.1 i
      have hn := hz i
      exact sub_pos.mpr (lt_of_le_of_ne hh hn)
    let S : ℝ := ∑ i, 1/(zstar i-zbar i)
    have hS : 0 < S := Finset.sum_pos (fun i _ => one_div_pos.mpr (hgap i)) Finset.univ_nonempty
    have hlam (i : Fin k) : lamBar zstar zbar i=(1/(zstar i-zbar i))*S⁻¹ := by simp [lamBar,hz,S]
    have hlpos (i : Fin k) : 0 < lamBar zstar zbar i := by rw [hlam]; exact mul_pos (one_div_pos.mpr (hgap i)) (inv_pos.mpr hS)
    have hprod (i : Fin k) : lamBar zstar zbar i*(zstar i-zbar i)=S⁻¹ := by
      rw [hlam]
      field_simp [ne_of_gt (hgap i)]
    have hsum : ∑ i, lamBar zstar zbar i=1 := by
      simp_rw [hlam]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ (ne_of_gt hS)
    have hbar : tcheb (lamBar zstar zbar) zstar zbar=S⁻¹ := by
      unfold tcheb
      simp_rw [hprod]
      simp
    have hforce (w : Fin k → ℝ) (hw : w∈Z)
        (hle : tcheb (lamBar zstar zbar) zstar w ≤ tcheb (lamBar zstar zbar) zstar zbar) : w=zbar := by
      apply nondom_eq_of_le Z zbar hzbar w hw
      intro i
      have hi := (Finset.le_sup' (fun i => lamBar zstar zbar i*(zstar i-w i)) (Finset.mem_univ i)).trans hle
      rw [hbar,← hprod i] at hi
      have hp := hlpos i
      nlinarith
    refine ⟨⟨fun i => (hlpos i).le,hsum⟩,?_,?_,?_⟩
    · rw [hbar]; positivity
    · intro w hw
      by_contra hn
      have hh : tcheb (lamBar zstar zbar) zstar w ≤ tcheb (lamBar zstar zbar) zstar zbar := le_of_lt (lt_of_not_ge hn)
      have he := hforce w hw hh
      subst w
      exact hn le_rfl
    · intro w hw hh; exact hforce w hw.1 hh
  · push_neg at hz
    obtain ⟨j,hj⟩ := hz
    have huniq := zero_unique Z zstar zbar hideal hzbar j hj
    have hn : ¬ ∀ i, zbar i≠zstar i := by intro h; exact h j hj
    have hlam : lamBar zstar zbar=(fun i => if j=i then 1 else 0) := by
      funext i
      simp only [lamBar,hn,ite_false]
      by_cases hi : j=i
      · subst i; simp [hj]
      · have hne : zbar i≠zstar i := by intro h; exact hi (huniq.2 i h).symm
        simp [hi,hne]
    have hval (w : Fin k → ℝ) (hw : w∈Z) : tcheb (lamBar zstar zbar) zstar w=zstar j-w j := by
      rw [hlam]
      apply le_antisymm
      · apply Finset.sup'_le
        intro i hi
        by_cases he : j=i
        · subst i; simp
        · simp only [he,ite_false,zero_mul]
          exact sub_nonneg.mpr (ideal_upper Z zstar hideal w hw j)
      · simpa only [tcheb,ite_true,one_mul] using Finset.le_sup' (fun i => (if j=i then (1 : ℝ) else 0)*(zstar i-w i)) (Finset.mem_univ j)
    have hbar : tcheb (lamBar zstar zbar) zstar zbar=0 := by rw [hval zbar hzbar.1,← hj,sub_self]
    refine ⟨?_,by rw [hbar],?_,?_⟩
    · rw [hlam]; exact ite_eq_mem_stdSimplex ℝ j
    · intro w hw
      rw [hbar,hval w hw]
      exact sub_nonneg.mpr (ideal_upper Z zstar hideal w hw j)
    · intro w hw hh
      rw [hval w hw.1,hbar] at hh
      apply huniq.1 w hw
      have hu := ideal_upper Z zstar hideal w hw.1 j
      linarith
private theorem tcheb_cont {k : ℕ} [NeZero k] (zstar lam : Fin k → ℝ) :
    Continuous (tcheb lam zstar) := by
  apply Continuous.finset_sup'_apply
  intro i hi
  exact continuous_const.mul (continuous_const.sub (continuous_apply i))

private theorem lex_exists {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hZ : IsCompact Z) (hZne : Z.Nonempty) : ∃ z, IsLexMin Z lam zstar z := by
  have hc := tcheb_cont zstar lam
  obtain ⟨z0,hz0,hmin⟩ := hZ.exists_isMinOn hZne hc.continuousOn
  let S : Set (Fin k → ℝ) := Z ∩ {z | tcheb lam zstar z ≤ tcheb lam zstar z0}
  have hS : IsCompact S := hZ.inter_right (isClosed_le hc continuous_const)
  have hSne : S.Nonempty := ⟨z0,hz0,by change tcheb lam zstar z0 ≤ tcheb lam zstar z0; exact le_rfl⟩
  have hcSum : Continuous (fun z : Fin k → ℝ => ∑ i, (zstar i-z i)) :=
    continuous_finset_sum _ (fun i _ => continuous_const.sub (continuous_apply i))
  obtain ⟨z,hz,hzmin⟩ := hS.exists_isMinOn hSne hcSum.continuousOn
  refine ⟨z,hz.1,?_,?_⟩
  · intro w hw
    exact hz.2.trans (hmin hw)
  · intro w hw hval
    exact hzmin ⟨hw,hval.trans hz.2⟩

private theorem lex_nondom {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (zstar lam : Fin k → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin k)) (z : Fin k → ℝ) (hz : IsLexMin Z lam zstar z) :
    z ∈ nondominated Z := by
  refine ⟨hz.1,?_⟩
  rintro ⟨w,hw,hdom⟩
  have hval : tcheb lam zstar w ≤ tcheb lam zstar z := by
    apply Finset.sup'_le
    intro i hi
    calc
      lam i*(zstar i-w i) ≤ lam i*(zstar i-z i) := mul_le_mul_of_nonneg_left (sub_le_sub_left (hdom.1 i) _) (hlam.1 i)
      _ ≤ tcheb lam zstar z := Finset.le_sup' (fun i => lam i*(zstar i-z i)) (Finset.mem_univ i)
  have hsum := hz.2.2 w hw hval
  have hstrict : ∑ i, (zstar i-w i) < ∑ i, (zstar i-z i) := by
    apply Finset.sum_lt_sum
    · intro i hi; linarith [hdom.1 i]
    · obtain ⟨i,hi⟩ := hdom.2
      exact ⟨i,Finset.mem_univ i,by linarith⟩
  linarith

theorem solution {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ)
    (hZc : IsCompact Z) (hideal : IsIdealVector Z zstar)
    (hzbar : zbar ∈ nondominated Z) :
    lamBar zstar zbar ∈ stdSimplex ℝ (Fin k) ∧
      IsLexMin Z (lamBar zstar zbar) zstar zbar ∧
      ∀ w, IsLexMin Z (lamBar zstar zbar) zstar w → w = zbar := by
  have hm := weight_model Z zstar zbar hideal hzbar
  obtain ⟨z,hz⟩ := lex_exists Z zstar (lamBar zstar zbar) hZc ⟨zbar,hzbar.1⟩
  have hzn := lex_nondom Z zstar (lamBar zstar zbar) hm.1 z hz
  have he : z=zbar := hm.2.2.2 z hzn (hz.2.1 zbar hzbar.1)
  subst z
  refine ⟨hm.1,hz,?_⟩
  intro w hw
  exact hm.2.2.2 w (lex_nondom Z zstar _ hm.1 w hw) (hw.2.1 zbar hzbar.1)
