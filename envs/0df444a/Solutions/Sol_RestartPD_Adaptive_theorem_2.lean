-- Prove2me | solution 1 for RestartPD.Adaptive.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T07:44:09.822986+00:00
-- url     : https://prove2.me/submissions/db9138bb-d8d8-4073-aba8-8fb0632e8c8a

-- Licensed under Apache 2.0. Full adaptive primal-dual restart theorem.
import Mathlib
import Definitions.Def_RestartPD_Adaptive_Restarts


open Set Filter
open RestartPD.Fixed

namespace AdaptiveRestartProof

variable {n m : ℕ} {L : Primal n → Dual m → ℝ}
  {X : Set (Primal n)} {Y : Set (Dual m)}

lemma distZ_nonneg (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m)) (z : E n m) :
    0 ≤ distZ L X Y p z := by
  have : Nonempty (Zstar L X Y) := hP.solution_nonempty.to_subtype
  exact le_ciInf fun s => apply_nonneg p _

lemma distZ_le (p : Seminorm ℝ (E n m)) (z s : E n m) (hs : s ∈ Zstar L X Y) :
    distZ L X Y p z ≤ p (z - s) := by
  exact ciInf_le (f := fun v : Zstar L X Y => p (z - (v : E n m)))
    ⟨(0 : ℝ), by rintro _ ⟨v, rfl⟩; exact apply_nonneg p _⟩ ⟨s, hs⟩

lemma distZ_eq_zero_of_mem (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (z : E n m) (hz : z ∈ Zstar L X Y) : distZ L X Y p z = 0 := by
  apply le_antisymm _ (distZ_nonneg hP p z)
  simpa using distZ_le p z z hz

end AdaptiveRestartProof


open Set Filter
open RestartPD.Fixed

namespace AdaptiveRestartProof

variable {n m : ℕ} {L : Primal n → Dual m → ℝ}
  {X : Set (Primal n)} {Y : Set (Dual m)}

lemma rhoPos_nonneg (p : Seminorm ℝ (E n m)) {z : E n m}
    (hz : z ∈ X ×ˢ Y) {r : ℝ} (hr : 0 < r) : 0 ≤ rhoPos L X Y p r z := by
  have hw : z ∈ Wball X Y p r z := ⟨hz, by simpa using hr.le⟩
  calc
    (0 : EReal) = ((gapAt L z z / r : ℝ) : EReal) := by simp [gapAt]
    _ ≤ rhoPos L X Y p r z := le_iSup_of_le z (le_iSup_of_le hw le_rfl)

lemma le_right_limsup {f : ℝ → EReal} {c : EReal}
    (h : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), c ≤ f r) :
    c ≤ Filter.limsup f (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  apply Filter.le_limsup_of_le (by isBoundedDefault)
  intro b hb
  obtain ⟨r, hr, hrb⟩ := (h.and hb).exists
  exact hr.trans hrb

lemma rho_nonneg (p : Seminorm ℝ (E n m)) {z : E n m}
    (hz : z ∈ X ×ˢ Y) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ rho L X Y p r z := by
  by_cases h0 : r = 0
  · simp only [rho, h0]
    apply le_right_limsup
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact rhoPos_nonneg p hz ht
  · simpa only [rho, if_neg h0] using rhoPos_nonneg p hz (lt_of_le_of_ne hr (Ne.symm h0))

lemma positive_gap_of_not_saddle {z : E n m} (hz : z ∈ X ×ˢ Y)
    (h : z ∉ Zstar L X Y) : ∃ w ∈ X ×ˢ Y, 0 < gapAt L z w := by
  by_contra! hn
  apply h
  refine ⟨hz, ?_⟩
  intro x hx y hy
  have hdual := hn (z.1, y) ⟨hz.1, hy⟩
  have hprimal := hn (x, z.2) ⟨hx, hz.2⟩
  constructor <;> simp only [gapAt] at hdual hprimal <;> linarith

lemma gap_convex_combination (hP : IsPDProblem L X Y) {z w : E n m}
    (hz : z ∈ X ×ˢ Y) (hw : w ∈ X ×ˢ Y) {t : ℝ} (ht : t ∈ Icc 0 1) :
    t * gapAt L z w ≤ gapAt L z ((1 - t) • z + t • w) := by
  have hp := (hP.convex_L z.2 hz.2).2 hz.1 hw.1 (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hd := (hP.concave_L z.1 hz.1).2 hz.2 hw.2 (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at hp hd
  change t * (L z.1 w.2 - L w.1 z.2) ≤
    L z.1 ((1-t) • z.2 + t • w.2) - L ((1-t) • z.1 + t • w.1) z.2
  nlinarith

end AdaptiveRestartProof


open Set Filter
open RestartPD.Fixed

namespace AdaptiveRestartProof

variable {n m : ℕ} {L : Primal n → Dual m → ℝ}
  {X : Set (Primal n)} {Y : Set (Dual m)}

lemma positive_uniform_rho (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    {z w : E n m} (hz : z ∈ X ×ˢ Y) (hw : w ∈ X ×ˢ Y)
    (hg : 0 < gapAt L z w) :
    ∃ R c : ℝ, 0 < R ∧ 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      (c : EReal) ≤ rhoPos L X Y p r z := by
  let R := max 1 (p (z-w))
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R, gapAt L z w / R, hR, div_pos hg hR, ?_⟩
  intro r hr hrR
  let t := r/R
  have ht0 : 0 ≤ t := (div_pos hr hR).le
  have ht1 : t ≤ 1 := (div_le_one hR).mpr hrR
  let v := (1-t) • z + t • w
  have hv : v ∈ X ×ˢ Y :=
    (hP.convex_X.prod hP.convex_Y) hz hw (sub_nonneg.mpr ht1) ht0 (by ring)
  have hvec : z-v = t • (z-w) := by dsimp [v]; module
  have hnorm : p (z-v) ≤ r := by
    rw [hvec, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      t * p (z-w) ≤ t * R := mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
      _ = r := by dsimp [t]; field_simp
  have hgap := gap_convex_combination hP hz hw ⟨ht0, ht1⟩
  have hquot : gapAt L z w / R ≤ gapAt L z v / r := by
    apply (le_div_iff₀ hr).mpr
    have heq : gapAt L z w / R * r = t * gapAt L z w := by dsimp [t]; ring
    rw [heq]
    exact hgap
  exact (EReal.coe_le_coe_iff.mpr hquot).trans
    (le_iSup_of_le v (le_iSup_of_le (show v ∈ Wball X Y p r z from ⟨hv, hnorm⟩) le_rfl))

lemma zero_radius_saddle (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    {z : E n m} (hz : z ∈ X ×ˢ Y) (hgap : rho L X Y p 0 z ≤ 0) :
    z ∈ Zstar L X Y := by
  by_contra hn
  obtain ⟨w, hw, hg⟩ := positive_gap_of_not_saddle hz hn
  obtain ⟨R, c, hR, hc, hbound⟩ := positive_uniform_rho hP p hz hw hg
  have he : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), (c : EReal) ≤ rhoPos L X Y p r z := by
    have hsmall : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), r < R :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hR)
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hbound r hr hrR.le
  have hl := le_right_limsup he
  have hzero : (c : EReal) ≤ 0 := hl.trans (by simpa [rho] using hgap)
  have : c ≤ 0 := EReal.coe_le_coe_iff.mp hzero
  exact (not_le_of_gt hc) this

lemma zero_radius_distance_zero (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    {z : E n m} (hz : z ∈ X ×ˢ Y) (hgap : rho L X Y p 0 z ≤ 0) :
    distZ L X Y p z = 0 :=
  distZ_eq_zero_of_mem hP p z (zero_radius_saddle hP p hz hgap)

end AdaptiveRestartProof


open RestartPD.Fixed RestartPD.Adaptive

namespace AdaptiveRestartProof

variable {n m : ℕ}
variable {L : Primal n → Dual m → ℝ} {X : Set (Primal n)} {Y : Set (Dual m)}
variable {p : Seminorm ℝ (E n m)} {Runs : E n m → Set (ℕ → E n m)}
variable {q C β : ℝ} {τ : ℕ → ℕ} {z : ℕ → E n m} {zb : ℕ → ℕ → E n m}

theorem interval_pos (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb) (k : ℕ) :
    1 ≤ τ k := by
  by_cases hk : k = 0
  · simpa [hk] using hrun.1
  · exact (hrun.2.2 k (by omega)).1

theorem outer_feasible (h3 : Property3 L X Y p Runs q C)
    (hz0 : z 0 ∈ X ×ˢ Y) (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (k : ℕ) : z k ∈ X ×ˢ Y := by
  induction k with
  | zero => exact hz0
  | succ k ih =>
    rw [(hrun.2.1 k).2]
    exact (h3.2.2 (z k) ih (zb k) (hrun.2.1 k).1 (τ k) (interval_pos hrun k)).1

theorem inner_estimates (h3 : Property3 L X Y p Runs q C)
    (hz0 : z 0 ∈ X ×ˢ Y) (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (k t : ℕ) (ht : 1 ≤ t) :
    zb k t ∈ X ×ˢ Y ∧
    rho L X Y p (p (zb k t - z k)) (zb k t) ≤
      ((2 * C * p (zb k t - z k) / t : ℝ) : EReal) ∧
    p (zb k t - z k) ≤ (q + 2) * distZ L X Y p (z k) :=
  h3.2.2 (z k) (outer_feasible h3 hz0 hrun k) (zb k) (hrun.2.1 k).1 t ht

theorem outer_estimates (h3 : Property3 L X Y p Runs q C)
    (hz0 : z 0 ∈ X ×ˢ Y) (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (k : ℕ) (hk : 1 ≤ k) :
    rho L X Y p (p (z k - z (k - 1))) (z k) ≤
      ((2 * C * p (z k - z (k - 1)) / τ (k - 1) : ℝ) : EReal) ∧
    p (z k - z (k - 1)) ≤ (q + 2) * distZ L X Y p (z (k - 1)) := by
  have he : zb (k - 1) (τ (k - 1)) = z k := by
    rw [← (hrun.2.1 (k - 1)).2, Nat.sub_add_cancel hk]
  simpa only [he] using
    (inner_estimates h3 hz0 hrun (k - 1) (τ (k - 1)) (interval_pos hrun (k - 1))).2

theorem gap_step (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (k : ℕ) (hk : 1 ≤ k) :
    rho L X Y p (p (z (k + 1) - z k)) (z (k + 1)) ≤
      (β : EReal) * rho L X Y p (p (z k - z (k - 1))) (z k) := by
  have h := (hrun.2.2 k hk).2.1
  unfold RestartCond at h
  simpa only [← (hrun.2.1 k).2] using h

theorem displacement_le_diameter {S : Set (E n m)} {x y : E n m}
    (hx : x ∈ S) (hy : y ∈ S) : (p (x - y) : EReal) ≤ diamS p S := by
  exact le_max_of_le_right (le_iSup_of_le x (le_iSup_of_le hx
    (le_iSup_of_le y (le_iSup_of_le hy le_rfl))))

end AdaptiveRestartProof


namespace AdaptiveRestartProof

theorem ceiling_estimates {q C α β : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hα : 0 < α) (hβ : 0 < β) :
    1 ≤ Nat.ceil (2 * C * (q + 2) / (α * β)) ∧
    2 * C * (q + 2) / (Nat.ceil (2 * C * (q + 2) / (α * β)) : ℝ) ≤ α * β := by
  have hv : 0 < 2 * C * (q + 2) / (α * β) := by positivity
  have ht : 1 ≤ Nat.ceil (2 * C * (q + 2) / (α * β)) := Nat.ceil_pos.mpr hv
  refine ⟨ht, ?_⟩
  have htR : (0 : ℝ) < Nat.ceil (2 * C * (q + 2) / (α * β)) := by exact_mod_cast ht
  apply (div_le_iff₀ htR).mpr
  have h := Nat.le_ceil (2 * C * (q + 2) / (α * β))
  have := (div_le_iff₀ (mul_pos hα hβ)).mp h
  nlinarith

theorem gap_geometric {G : ℕ → EReal} {β B : ℝ} (hβ : 0 ≤ β)
    (hfirst : G 1 ≤ (B : EReal))
    (hstep : ∀ k, 1 ≤ k → G (k + 1) ≤ (β : EReal) * G k)
    (k : ℕ) (hk : 1 ≤ k) : G k ≤ ((β ^ (k - 1) * B : ℝ) : EReal) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => simpa using hfirst
  | succ j ih =>
    have hs := hstep (1 + j) (by omega)
    have hm := mul_le_mul_of_nonneg_left (ih (by omega)) (show (0 : EReal) ≤ (β : EReal) by exact_mod_cast hβ)
    refine hs.trans ?_
    convert hm using 1
    simp only [Nat.add_sub_cancel_left, ← EReal.coe_mul, pow_succ]
    congr 1
    ring

theorem distance_rate {q C α β d₀ d : ℝ} {t₀ k : ℕ}
    (_hq : 0 < q) (_hC : 0 < C) (hα : 0 < α) (hβ : 0 < β)
    (hd₀ : 0 ≤ d₀) (ht₀ : 1 ≤ t₀) (hk : 1 ≤ k)
    (hgap : α * d ≤ β ^ (k - 1) * (2 * C * (q + 2) * d₀ / t₀)) :
    d ≤ β ^ k * ((Nat.ceil (2 * C * (q + 2) / (α * β)) : ℝ) / t₀) * d₀ := by
  have htR : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have hceil := Nat.le_ceil (2 * C * (q + 2) / (α * β))
  have hc := (div_le_iff₀ (mul_pos hα hβ)).mp hceil
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ β ^ (k - 1) * d₀ / t₀ by positivity)
  have hp : β ^ k = β ^ (k - 1) * β := by rw [← pow_succ, Nat.sub_add_cancel hk]
  apply (mul_le_mul_iff_right₀ hα).mp
  refine hgap.trans ?_
  rw [hp]
  convert hm using 1 <;> ring

end AdaptiveRestartProof


open RestartPD.Fixed RestartPD.Adaptive

namespace AdaptiveRestartProof

variable {n m : ℕ}
variable {L : Primal n → Dual m → ℝ} {X : Set (Primal n)} {Y : Set (Dual m)}
variable {p : Seminorm ℝ (E n m)} {Runs : E n m → Set (ℕ → E n m)}
variable {q C α β : ℝ} {τ : ℕ → ℕ} {z : ℕ → E n m} {zb : ℕ → ℕ → E n m}

theorem outer_sharpness (hP : IsPDProblem L X Y) (h3 : Property3 L X Y p Runs q C)
    (hz0 : z 0 ∈ X ×ˢ Y) (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    {S : Set (E n m)} (hzS : ∀ k, z k ∈ S) (hsharp : IsSharpOn L X Y p α S)
    (k : ℕ) (hk : 1 ≤ k) :
    ((α * distZ L X Y p (z k) : ℝ) : EReal) ≤
      rho L X Y p (p (z k - z (k - 1))) (z k) := by
  have hz := outer_feasible h3 hz0 hrun k
  by_cases hr : p (z k - z (k - 1)) = 0
  · have hb := (outer_estimates h3 hz0 hrun k hk).1
    rw [hr] at hb ⊢
    have hg : rho L X Y p 0 (z k) ≤ 0 := by simpa using hb
    have hd := zero_radius_distance_zero hP p hz hg
    simpa [hd] using rho_nonneg p hz (show (0 : ℝ) ≤ 0 by rfl)
  · exact hsharp.2 _ (lt_of_le_of_ne (apply_nonneg p _) (Ne.symm hr))
      (displacement_le_diameter (hzS k) (hzS (k - 1))) _ (hzS k)

end AdaptiveRestartProof


open RestartPD.Fixed RestartPD.Adaptive

namespace AdaptiveRestartProof

variable {n m : ℕ}
variable {L : Primal n → Dual m → ℝ} {X : Set (Primal n)} {Y : Set (Dual m)}
variable {p : Seminorm ℝ (E n m)} {Runs : E n m → Set (ℕ → E n m)}
variable {q C α β : ℝ} {τ : ℕ → ℕ} {z : ℕ → E n m} {zb : ℕ → ℕ → E n m}

theorem trigger_at_ceiling (hP : IsPDProblem L X Y) (h3 : Property3 L X Y p Runs q C)
    (hα : 0 < α) (hβ : 0 < β) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    {S : Set (E n m)} (hzS : ∀ k, z k ∈ S) (hsharp : IsSharpOn L X Y p α S)
    (k : ℕ) (hk : 1 ≤ k) :
    RestartCond L X Y p β z zb k (Nat.ceil (2 * C * (q + 2) / (α * β))) := by
  let T := Nat.ceil (2 * C * (q + 2) / (α * β))
  have ht := ceiling_estimates h3.1 h3.2.1 hα hβ
  have hT : (0 : ℝ) < T := by exact_mod_cast ht.1
  have hi := inner_estimates h3 hz0 hrun k T ht.1
  have hd : 0 ≤ distZ L X Y p (z k) := distZ_nonneg hP p (z k)
  have hC := h3.2.1
  have hc : 0 ≤ 2 * C := by positivity
  have hu : 2 * C * p (zb k T - z k) / T ≤ α * β * distZ L X Y p (z k) := by
    calc
      _ ≤ 2 * C * ((q + 2) * distZ L X Y p (z k)) / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi.2.2 hc) hT.le
      _ = (2 * C * (q + 2) / T) * distZ L X Y p (z k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ht.2 hd
  have hs := outer_sharpness hP h3 hz0 hrun hzS hsharp k hk
  have hm := mul_le_mul_of_nonneg_left hs (show (0 : EReal) ≤ (β : EReal) by exact_mod_cast hβ.le)
  unfold RestartCond
  refine hi.2.1.trans ((EReal.coe_le_coe_iff.mpr hu).trans ?_)
  convert hm using 1
  rw [← EReal.coe_mul]
  congr 1
  ring

theorem interval_le_ceiling (hP : IsPDProblem L X Y) (h3 : Property3 L X Y p Runs q C)
    (hα : 0 < α) (hβ : 0 < β) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    {S : Set (E n m)} (hzS : ∀ k, z k ∈ S) (hsharp : IsSharpOn L X Y p α S)
    (k : ℕ) (hk : 1 ≤ k) : τ k ≤ Nat.ceil (2 * C * (q + 2) / (α * β)) := by
  by_contra h
  exact (hrun.2.2 k hk).2.2 _ (ceiling_estimates h3.1 h3.2.1 hα hβ).1
    (Nat.lt_of_not_ge h) (trigger_at_ceiling hP h3 hα hβ hz0 hrun hzS hsharp k hk)

end AdaptiveRestartProof


open RestartPD.Fixed RestartPD.Adaptive

namespace AdaptiveRestartProof

variable {n m : ℕ}
variable {L : Primal n → Dual m → ℝ} {X : Set (Primal n)} {Y : Set (Dual m)}
variable {p : Seminorm ℝ (E n m)} {Runs : E n m → Set (ℕ → E n m)}
variable {q C α β : ℝ} {τ : ℕ → ℕ} {z : ℕ → E n m} {zb : ℕ → ℕ → E n m}

theorem distance_contraction (hP : IsPDProblem L X Y) (h3 : Property3 L X Y p Runs q C)
    (hα : 0 < α) (hβ : 0 < β) (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    {S : Set (E n m)} (hzS : ∀ k, z k ∈ S) (hsharp : IsSharpOn L X Y p α S)
    (k : ℕ) (hk : 1 ≤ k) :
    distZ L X Y p (z k) ≤ β ^ k *
      ((Nat.ceil (2 * C * (q + 2) / (α * β)) : ℝ) / (τ 0 : ℝ)) * distZ L X Y p (z 0) := by
  let G := fun j => rho L X Y p (p (z j - z (j - 1))) (z j)
  have he := outer_estimates h3 hz0 hrun 1 (by omega)
  simp only [Nat.sub_self] at he
  have hC := h3.2.1
  have ht : (0 : ℝ) ≤ τ 0 := by positivity
  have hc : 0 ≤ 2 * C := by positivity
  have hf : G 1 ≤ ((2 * C * (q + 2) * distZ L X Y p (z 0) / τ 0 : ℝ) : EReal) := by
    refine he.1.trans (EReal.coe_le_coe_iff.mpr ?_)
    calc
      _ ≤ 2 * C * ((q + 2) * distZ L X Y p (z 0)) / τ 0 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he.2 hc) ht
      _ = _ := by ring
  have hs : ∀ j, 1 ≤ j → G (j + 1) ≤ (β : EReal) * G j := by
    intro j hj
    simpa only [G, Nat.add_sub_cancel] using gap_step hrun j hj
  have hg := gap_geometric hβ.le hf hs k hk
  have ha := outer_sharpness hP h3 hz0 hrun hzS hsharp k hk
  have hreal := EReal.coe_le_coe_iff.mp (ha.trans hg)
  exact distance_rate h3.1 hC hα hβ (distZ_nonneg hP p (z 0)) hrun.1 hk hreal

end AdaptiveRestartProof


namespace RestartPD.Adaptive

/-- Theorem 2, p. 18: adaptive restart lengths and distance decay. -/
theorem adaptive_restart_complete {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (hP : RestartPD.Fixed.IsPDProblem L X Y)
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (q C : ℝ) (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (S : Set (RestartPD.Fixed.E n m)) (hzS : ∀ k, z k ∈ S)
    (hsharp : RestartPD.Fixed.IsSharpOn L X Y p α S) :
    let tstar := Nat.ceil (2 * C * (q + 2) / (α * β))
    ∀ k : ℕ, 1 ≤ k →
      τ k ≤ tstar ∧
        RestartPD.Fixed.distZ L X Y p (z k) ≤
          β ^ k * ((tstar : ℝ) / (τ 0 : ℝ)) * RestartPD.Fixed.distZ L X Y p (z 0) := by
  dsimp only
  intro k hk
  exact ⟨AdaptiveRestartProof.interval_le_ceiling hP h3 hα hβ.1 hz0 hrun hzS hsharp k hk,
    AdaptiveRestartProof.distance_contraction hP h3 hα hβ.1 hz0 hrun hzS hsharp k hk⟩

end RestartPD.Adaptive


namespace RestartPD.Adaptive

/-- Theorem 2, p. 18: adaptive restart lengths and distance decay. -/
theorem theorem_2 {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (hP : RestartPD.Fixed.IsPDProblem L X Y)
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (q C : ℝ) (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (S : Set (RestartPD.Fixed.E n m)) (hzS : ∀ k, z k ∈ S)
    (hsharp : RestartPD.Fixed.IsSharpOn L X Y p α S) :
    let tstar := Nat.ceil (2 * C * (q + 2) / (α * β))
    ∀ k : ℕ, 1 ≤ k →
      τ k ≤ tstar ∧
        RestartPD.Fixed.distZ L X Y p (z k) ≤
          β ^ k * ((tstar : ℝ) / (τ 0 : ℝ)) * RestartPD.Fixed.distZ L X Y p (z 0) := by
  exact adaptive_restart_complete L X Y hP p Runs q C h3 α β hα hβ τ z zb hz0 hrun S hzS hsharp

end RestartPD.Adaptive

open RestartPD.Adaptive

theorem solution {n m : ℕ}
    (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (hP : RestartPD.Fixed.IsPDProblem L X Y)
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (q C : ℝ) (h3 : RestartPD.Fixed.Property3 L X Y p Runs q C)
    (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m)
    (hz0 : z 0 ∈ X ×ˢ Y)
    (hrun : IsAdaptiveRestartRun L X Y p Runs β τ z zb)
    (S : Set (RestartPD.Fixed.E n m)) (hzS : ∀ k, z k ∈ S)
    (hsharp : RestartPD.Fixed.IsSharpOn L X Y p α S) :
    let tstar := Nat.ceil (2 * C * (q + 2) / (α * β))
    ∀ k : ℕ, 1 ≤ k →
      τ k ≤ tstar ∧
        RestartPD.Fixed.distZ L X Y p (z k) ≤
          β ^ k * ((tstar : ℝ) / (τ 0 : ℝ)) * RestartPD.Fixed.distZ L X Y p (z 0) := RestartPD.Adaptive.theorem_2 L X Y hP p Runs q C h3 α β hα hβ τ z zb hz0 hrun S hzS hsharp
