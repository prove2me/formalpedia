-- Prove2me | solution 1 for RestartPD.Fixed.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:25:02.049976+00:00
-- url     : https://prove2.me/submissions/151f823f-e1af-4623-b4b8-f19f5df8c167

import Mathlib
import Definitions.Def_RestartPD_Fixed_Algorithms

open RestartPD.Fixed Set Filter

namespace TwentyAnalysis.Restart

variable {n m : ℕ}

lemma mix_feasible (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y) (z w : E n m)
    (hz : z ∈ X ×ˢ Y) (hw : w ∈ X ×ˢ Y) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (1-a) • z + a • w ∈ X ×ˢ Y := by
  exact ⟨hX hz.1 hw.1 (sub_nonneg.mpr ha1) ha (by ring),
    hY hz.2 hw.2 (sub_nonneg.mpr ha1) ha (by ring)⟩

lemma gap_mix (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (z w : E n m) (hz : z ∈ X ×ˢ Y) (hw : w ∈ X ×ˢ Y)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a * gapAt L z w ≤ gapAt L z ((1-a) • z + a • w) := by
  have hx := (hLx z.2 hz.2).2 hz.1 hw.1 (sub_nonneg.mpr ha1) ha (show 1-a+a=1 by ring)
  have hy := (hLy z.1 hz.1).2 hz.2 hw.2 (sub_nonneg.mpr ha1) ha (show 1-a+a=1 by ring)
  simp only [smul_eq_mul] at hx hy
  change a * (L z.1 w.2 - L w.1 z.2) ≤
    L z.1 ((1-a) • z.2 + a • w.2) - L ((1-a) • z.1 + a • w.1) z.2
  linarith

lemma mix_distance (p : Seminorm ℝ (E n m)) (z w : E n m) (a : ℝ) (ha : 0 ≤ a) :
    p (z - ((1-a) • z + a • w)) = a * p (z-w) := by
  have he : z - ((1-a) • z + a • w) = a • (z-w) := by module
  rw [he, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha]

lemma rhoPos_nonneg (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ rhoPos L X Y p r z := by
  have hm : z ∈ Wball X Y p r z := ⟨hz, by simpa using hr⟩
  have he : ((gapAt L z z / r : ℝ) : EReal) = 0 := by simp [gapAt]
  rw [← he]
  exact le_iSup_of_le z (le_iSup_of_le hm le_rfl)

lemma rhoPos_antitone (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y)
    (r s : ℝ) (hr : 0 < r) (hs : r ≤ s) :
    rhoPos L X Y p s z ≤ rhoPos L X Y p r z := by
  have hs0 : 0 < s := hr.trans_le hs
  have ha : 0 ≤ r/s := le_of_lt (div_pos hr hs0)
  have ha1 : r/s ≤ 1 := (div_le_one hs0).mpr hs
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  let v := (1-r/s) • z + (r/s) • w
  have hv : v ∈ Wball X Y p r z := by
    refine ⟨mix_feasible X Y hX hY z w hz hw.1 _ ha ha1, ?_⟩
    rw [mix_distance p z w _ ha]
    calc
      r / s * p (z-w) ≤ r/s*s := mul_le_mul_of_nonneg_left hw.2 ha
      _ = r := div_mul_cancel₀ _ (ne_of_gt hs0)
  have hg := gap_mix L X Y hLx hLy z w hz hw.1 _ ha ha1
  have hdiv : gapAt L z w / s ≤ gapAt L z v / r := by
    apply (le_div_iff₀ hr).mpr
    calc
      gapAt L z w / s * r = r/s * gapAt L z w := by ring
      _ ≤ gapAt L z v := hg
  exact le_trans (EReal.coe_le_coe_iff.mpr hdiv) (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

lemma rhoPos_le_zeroRadius (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y)
    (r : ℝ) (hr : 0 < r) :
    rhoPos L X Y p r z ≤ rho L X Y p 0 z := by
  simp only [rho, if_pos rfl]
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  have hpos : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), 0 < s := self_mem_nhdsWithin
  have hlt : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < r :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)
  filter_upwards [hpos, hlt] with s hs hsr
  exact rhoPos_antitone L X Y hX hY hLx hLy p z hz s r hs (le_of_lt hsr)

lemma prop5 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) :
    AntitoneOn (fun r : ℝ => rho L X Y p r z) (Ici 0) := by
  intro r hr s hs hrs
  by_cases hs0 : s = 0
  · have hr0 : r = 0 := le_antisymm (hs0 ▸ hrs) hr
    simp [hs0, hr0]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  by_cases hr0 : r = 0
  · subst r
    simpa [rho, hs0] using rhoPos_le_zeroRadius L X Y hX hY hLx hLy p z hz s hspos
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    simpa [rho, hr0, hs0] using rhoPos_antitone L X Y hX hY hLx hLy p z hz r s hrpos hrs

lemma pdGap_nonneg (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (z : E n m) (hz : z ∈ X ×ˢ Y) : 0 ≤ pdGap L X Y z := by
  have he : ((gapAt L z z : ℝ) : EReal) = 0 := by simp [gapAt]
  rw [← he]
  exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)

lemma gap_nonpos_of_zero (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (z : E n m) (h : pdGap L X Y z = 0) (w : E n m) (hw : w ∈ X ×ˢ Y) : gapAt L z w ≤ 0 := by
  have hg : ((gapAt L z w : ℝ) : EReal) ≤ pdGap L X Y z := le_iSup_of_le w (le_iSup_of_le hw le_rfl)
  rw [h] at hg
  exact EReal.coe_le_coe_iff.mp hg

lemma rhoPos_zero_of_gap_zero (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y)
    (h : pdGap L X Y z = 0) (r : ℝ) (hr : 0 < r) : rhoPos L X Y p r z = 0 := by
  apply le_antisymm ?_ (rhoPos_nonneg L X Y p z hz r hr.le)
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  exact EReal.coe_le_coe_iff.mpr (div_nonpos_of_nonpos_of_nonneg (gap_nonpos_of_zero L X Y z h w hw.1) hr.le)

lemma gap_zero_of_rhoPos_zero (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y)
    (r : ℝ) (hr : 0 < r) (hzero : rhoPos L X Y p r z = 0) : pdGap L X Y z = 0 := by
  apply le_antisymm ?_ (pdGap_nonneg L X Y z hz)
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  let s := p (z-w) + r
  have hs : 0 < s := add_pos_of_nonneg_of_pos (apply_nonneg p _) hr
  have hrs : r ≤ s := by dsimp [s]; linarith [apply_nonneg p (z-w)]
  have hwball : w ∈ Wball X Y p s z := ⟨hw, by dsimp [s]; linarith⟩
  have hle : ((gapAt L z w / s : ℝ) : EReal) ≤ 0 := by
    calc
      _ ≤ rhoPos L X Y p s z := le_iSup_of_le w (le_iSup_of_le hwball le_rfl)
      _ ≤ rhoPos L X Y p r z := rhoPos_antitone L X Y hX hY hLx hLy p z hz r s hr hrs
      _ = 0 := hzero
  apply EReal.coe_le_coe_iff.mpr
  have hd := EReal.coe_le_coe_iff.mp hle
  simpa using (div_le_iff₀ hs).mp hd

lemma prop6 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) (r : ℝ) (hr : 0 ≤ r) :
    pdGap L X Y z = 0 ↔ rho L X Y p r z = 0 := by
  constructor
  · intro h
    by_cases hr0 : r = 0
    · simp only [rho, hr0, if_pos rfl]
      have he : (fun s : ℝ => rhoPos L X Y p s z) =ᶠ[nhdsWithin 0 (Ioi 0)] (fun _ => (0 : EReal)) := by
        filter_upwards [show ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), 0 < s from self_mem_nhdsWithin] with s hs
        exact rhoPos_zero_of_gap_zero L X Y p z hz h s hs
      rw [Filter.limsup_congr he, Filter.limsup_const]
      simp
    · simpa [rho, hr0] using rhoPos_zero_of_gap_zero L X Y p z hz h r (lt_of_le_of_ne hr (Ne.symm hr0))
  · intro h
    by_cases hr0 : r = 0
    · have hle := rhoPos_le_zeroRadius L X Y hX hY hLx hLy p z hz 1 (by norm_num)
      rw [hr0] at h
      rw [h] at hle
      have hz1 : rhoPos L X Y p 1 z = 0 := le_antisymm hle (rhoPos_nonneg L X Y p z hz 1 (by norm_num))
      exact gap_zero_of_rhoPos_zero L X Y hX hY hLx hLy p z hz 1 (by norm_num) hz1
    · exact gap_zero_of_rhoPos_zero L X Y hX hY hLx hLy p z hz r (lt_of_le_of_ne hr (Ne.symm hr0)) (by simpa [rho, hr0] using h)

lemma rho_nonneg (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ rho L X Y p r z := by
  by_cases hr0 : r = 0
  · simp only [rho, hr0, if_pos rfl]
    apply Filter.le_limsup_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [show ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), 0 < s from self_mem_nhdsWithin] with s hs
    exact rhoPos_nonneg L X Y p z hz s hs.le
  · simpa [rho, hr0] using rhoPos_nonneg L X Y p z hz r hr

lemma saddle_of_gap_zero (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (z : E n m) (hz : z ∈ X ×ˢ Y) (h : pdGap L X Y z = 0) : z ∈ Zstar L X Y := by
  refine ⟨hz, fun x hx y hy => ?_⟩
  have h1 := gap_nonpos_of_zero L X Y z h (z.1,y) ⟨hz.1,hy⟩
  have h2 := gap_nonpos_of_zero L X Y z h (x,z.2) ⟨hx,hz.2⟩
  dsimp [gapAt] at h1 h2
  exact ⟨by linarith, by linarith⟩

lemma prop8 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (z0 : E n m) (hz0 : z0 ∈ X ×ˢ Y) (zb : ℕ → E n m) (hzb : zb ∈ Runs z0)
    (t : ℕ) (ht : 1 ≤ t) (hzero : p (zb t-z0)=0) : zb t ∈ Zstar L X Y := by
  obtain ⟨hz,hgap,_⟩ := h3.2.2 z0 hz0 zb hzb t ht
  have hzrho : rho L X Y p 0 (zb t) = 0 := by
    apply le_antisymm ?_ (rho_nonneg L X Y p (zb t) hz 0 le_rfl)
    simpa [hzero] using hgap
  apply saddle_of_gap_zero L X Y _ hz
  exact (prop6 L X Y hP.convex_X hP.convex_Y hP.convex_L hP.concave_L p (zb t) hz 0 le_rfl).mpr hzrho

lemma dist_nonneg (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) : 0 ≤ distZ L X Y p z :=
  Real.iInf_nonneg (fun _ => apply_nonneg p _)

lemma dist_zero (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ Zstar L X Y) : distZ L X Y p z = 0 := by
  apply le_antisymm ?_ (dist_nonneg L X Y p z)
  have hb : BddBelow (range (fun w : Zstar L X Y => p (z - (w : E n m)))) :=
    ⟨0, fun _ ⟨w,hw⟩ => hw ▸ apply_nonneg p _⟩
  exact (ciInf_le hb ⟨z,hz⟩).trans (by simp)

lemma restart_length_pos (q C α β : ℝ) (hq : 0 < q) (hC : 0 < C) (hα : 0 < α) (hβ : 0 < β) :
    1 ≤ Nat.ceil (2*C*(q+2)/(α*β)) := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (mul_pos (by norm_num) hC) (by linarith)) (mul_pos hα hβ)

lemma eq32 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs (Nat.ceil (2 * C * (q + 2) / (α * β))) z zb)
    (hsharp : IsSharpOn L X Y p α
      (Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0)))
    (N : ℕ)
    (hN : z N ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0))
    (hN1 : z (N + 1) ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0)) :
    distZ L X Y p (z (N + 1)) ≤ β * distZ L X Y p (z N) := by
  let t := Nat.ceil (2*C*(q+2)/(α*β))
  have ht : 1 ≤ t := restart_length_pos q C α β h3.1 h3.2.1 hα hβ.1
  have htR : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t from ht)
  have hr : z (N+1) = zb N t := (hrun N).2
  obtain ⟨hfeas,hgap,hstep⟩ := h3.2.2 (z N) hN.1 (zb N) (hrun N).1 t ht
  rw [← hr] at hgap hstep
  by_cases hzero : p (z (N+1)-z N)=0
  · have hzstar : z (N+1) ∈ Zstar L X Y := by
      rw [hr]
      exact prop8 L X Y hP p Runs q C h3 (z N) hN.1 (zb N) (hrun N).1 t ht (by simpa [← hr] using hzero)
    rw [dist_zero L X Y p _ hzstar]
    exact mul_nonneg hβ.1.le (dist_nonneg L X Y p _)
  · have hdpos : 0 < p (z (N+1)-z N) := lt_of_le_of_ne (apply_nonneg p _) (Ne.symm hzero)
    have hdiam : ((p (z (N+1)-z N) : ℝ) : EReal) ≤
        diamS p (Wball X Y p ((q+2)/(1-β)*distZ L X Y p (z 0)) (z 0)) := by
      apply le_trans ?_ (le_max_right _ _)
      exact le_iSup_of_le (z (N+1)) (le_iSup_of_le hN1 (le_iSup_of_le (z N) (le_iSup_of_le hN le_rfl)))
    have hs := hsharp.2 _ hdpos hdiam _ hN1
    have hreal : α * distZ L X Y p (z (N+1)) ≤ 2*C*p (z (N+1)-z N)/(t : ℝ) :=
      EReal.coe_le_coe_iff.mp (hs.trans hgap)
    have hc : 2*C*(q+2)/(α*β) ≤ (t : ℝ) := Nat.le_ceil _
    have hc' : 2*C*(q+2) ≤ (t : ℝ)*(α*β) := (div_le_iff₀ (mul_pos hα hβ.1)).mp hc
    have hd0 := dist_nonneg L X Y p (z N)
    have ha := (le_div_iff₀ htR).mp hreal
    have hb := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2*C by linarith [h3.2.1])
    have hc'' := mul_le_mul_of_nonneg_right hc' hd0
    apply (mul_le_mul_iff_right₀ (mul_pos hα htR)).mp
    nlinarith

lemma main (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs (Nat.ceil (2*C*(q+2)/(α*β))) z zb)
    (hsharp : IsSharpOn L X Y p α
      (Wball X Y p ((q+2)/(1-β)*distZ L X Y p (z 0)) (z 0)))
    (hsum : ∀ N : ℕ, (∀ k ≤ N, distZ L X Y p (z k) ≤ β^k*distZ L X Y p (z 0)) →
      z (N+1) ∈ Wball X Y p ((q+2)/(1-β)*distZ L X Y p (z 0)) (z 0)) :
    ∀ k : ℕ, distZ L X Y p (z k) ≤ β^k*distZ L X Y p (z 0) := by
  suffices hboth : ∀ k : ℕ, distZ L X Y p (z k) ≤ β^k*distZ L X Y p (z 0) ∧
      z k ∈ Wball X Y p ((q+2)/(1-β)*distZ L X Y p (z 0)) (z 0) from fun k => (hboth k).1
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      refine ⟨by simp, hz0, ?_⟩
      simp only [sub_self, map_zero]
      exact mul_nonneg (div_nonneg (by linarith [h3.1]) (sub_nonneg.mpr hβ.2.le)) (dist_nonneg L X Y p _)
    | succ N =>
      have hN := ih N (Nat.lt_succ_self N)
      have hN1 := hsum N (fun k hk => (ih k (Nat.lt_succ_of_le hk)).1)
      refine ⟨?_, hN1⟩
      calc
        distZ L X Y p (z (N+1)) ≤ β*distZ L X Y p (z N) :=
          eq32 L X Y hP p Runs q C h3 α β hα hβ z zb hz0 hrun hsharp N hN.2 hN1
        _ ≤ β*(β^N*distZ L X Y p (z 0)) := mul_le_mul_of_nonneg_left hN.1 hβ.1.le
        _ = β^(N+1)*distZ L X Y p (z 0) := by ring

end TwentyAnalysis.Restart


open RestartPD.Fixed
open scoped BigOperators

lemma TwentyAnalysis.Restart.partialSum {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n))
    (Y : Set (Dual m)) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (tstar : ℕ) (htstar : 1 ≤ tstar)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs tstar z zb)
    (N : ℕ) (hind : ∀ k ≤ N, distZ L X Y p (z k) ≤ β ^ k * distZ L X Y p (z 0)) :
    p (z (N + 1) - z 0) ≤ (q + 2) / (1 - β) * distZ L X Y p (z 0) ∧
      z (N + 1) ∈ Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0) := by
  have hq : 0 < q + 2 := by linarith [h3.1]
  have hz (k : ℕ) : z k ∈ X ×ˢ Y := by
    induction k with
    | zero => exact hz0
    | succ k ih =>
      rw [(hrun k).2]
      exact (h3.2.2 (z k) ih (zb k) (hrun k).1 tstar htstar).1
  have hstep (k : ℕ) : p (z (k + 1) - z k) ≤ (q + 2) * distZ L X Y p (z k) := by
    rw [(hrun k).2]
    exact (h3.2.2 (z k) (hz k) (zb k) (hrun k).1 tstar htstar).2.2
  have hd : 0 ≤ distZ L X Y p (z 0) := by
    exact (mul_nonneg_iff_of_pos_left hq).mp ((apply_nonneg p _).trans (hstep 0))
  have hsum (t : ℕ) :
      p (z t - z 0) ≤ ∑ k ∈ Finset.range t, p (z (k + 1) - z k) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have he : z (t + 1) - z 0 = (z (t + 1) - z t) + (z t - z 0) := by abel
      rw [he, Finset.sum_range_succ]
      exact (map_add_le_add p _ _).trans (by linarith)
  have hg : ∑ k ∈ Finset.range (N + 1), β ^ k ≤ 1 / (1 - β) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) hβ.1.le hβ.2)
  have hbound : p (z (N + 1) - z 0) ≤ (q + 2) / (1 - β) * distZ L X Y p (z 0) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), p (z (k + 1) - z k) := hsum (N + 1)
      _ ≤ ∑ k ∈ Finset.range (N + 1), (q + 2) * (β ^ k * distZ L X Y p (z 0)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hstep k).trans (mul_le_mul_of_nonneg_left (hind k (by
          have := Finset.mem_range.mp hk
          omega)) hq.le)
      _ = ((q + 2) * distZ L X Y p (z 0)) * ∑ k ∈ Finset.range (N + 1), β ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ((q + 2) * distZ L X Y p (z 0)) * (1 / (1 - β)) :=
        mul_le_mul_of_nonneg_left hg (mul_nonneg hq.le hd)
      _ = _ := by ring
  refine ⟨hbound, hz (N + 1), ?_⟩
  have hsymm : p (z 0 - z (N + 1)) = p (z (N + 1) - z 0) := by
    simpa only [neg_sub] using (map_neg_eq_map p (z (N + 1) - z 0))
  simpa only [hsymm] using hbound

theorem solution {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (z : ℕ → E n m) (zb : ℕ → ℕ → E n m) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsFixedRestartRun Runs (Nat.ceil (2 * C * (q + 2) / (α * β))) z zb)
    (hsharp : IsSharpOn L X Y p α
      (Wball X Y p ((q + 2) / (1 - β) * distZ L X Y p (z 0)) (z 0))) :
    ∀ k : ℕ, distZ L X Y p (z k) ≤ β ^ k * distZ L X Y p (z 0) := by
  apply TwentyAnalysis.Restart.main L X Y hP p Runs q C h3 α β hα hβ z zb hz0 hrun hsharp
  intro N hind
  exact (TwentyAnalysis.Restart.partialSum L X Y p Runs q C h3 β hβ
    (Nat.ceil (2*C*(q+2)/(α*β)))
    (TwentyAnalysis.Restart.restart_length_pos q C α β h3.1 h3.2.1 hα hβ.1)
    z zb hz0 hrun N hind).2
