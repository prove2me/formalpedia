-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.verifiedNamedScore
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:42.883027+00:00
-- url     : https://prove2.me/submissions/41635673-ad71-452a-b4c4-30529ee5e954

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLow
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondLow
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalFirst
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_verifiedCanonicalSecond
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_verifiedMassIntervals
set_option Elab.async false
section
set_option autoImplicit true

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
noncomputable section

def Piece.slope (p : Piece) (x : ℝ) : ℝ := horner p.slopeCoeffs (x-p.lo)
theorem cast_qhorner (cs : List ℚ) (x : ℚ) :
    (qhorner cs x : ℝ) = horner cs x := by
  induction cs with
  | nil => simp [qhorner,horner]
  | cons a cs ih => simpa [qhorner,horner] using congrArg (fun u : ℝ => (a:ℝ)+(x:ℝ)*u) ih

theorem Piece.cast_qvalue (p : Piece) (x : ℚ) : (p.qvalue x : ℝ)=p.value x := by
  simp [qvalue,value,cast_qhorner]
theorem Piece.cast_qprimitive (p : Piece) (x : ℚ) : (p.qprimitive x : ℝ)=p.primitiveValue x := by
  simp [qprimitive,primitiveValue,cast_qhorner]

def lower (cs : List ℚ) (width : ℚ) : ℚ :=
  cs.foldr (fun a v => a + width * min v 0) 0

theorem lower_le_horner (cs : List ℚ) {w : ℚ} {x : ℝ}
    (hx : 0 ≤ x) (hxw : x ≤ (w:ℝ)) : (lower cs w : ℝ) ≤ horner cs x := by
  induction cs with
  | nil => simp [lower,horner]
  | cons a cs ih =>
    change ((a+w*min (lower cs w) 0 : ℚ):ℝ) ≤ a + x*horner cs x
    push_cast
    apply add_le_add_right
    calc
      _ ≤ x * min (lower cs w : ℝ) 0 := mul_le_mul_of_nonpos_right hxw (min_le_right _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left ((min_le_left _ _).trans ih) hx

theorem hasDeriv_horner (cs : List ℚ) (x : ℝ) :
    ∃ y, HasDerivAt (horner cs) y x := by
  induction cs with
  | nil => exact ⟨0,hasDerivAt_const _ _⟩
  | cons a cs ih =>
    obtain ⟨y,hy⟩ := ih
    exact ⟨_, ((hasDerivAt_id _).mul hy).const_add _⟩

theorem Piece.continuous_value (p : Piece) : Continuous p.value := by
  exact (continuous_iff_continuousAt.mpr fun x => (hasDeriv_horner (pad p.c) x).choose_spec.continuousAt).comp (continuous_id.sub continuous_const)

private theorem horner_step {f : ℝ → ℝ} {f' : ℝ} (a b x : ℝ) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => a+(y-b)*f y) (f x + (x-b)*f') x := by
  simpa using (((hasDerivAt_id x).sub_const b).mul hf).const_add a

theorem Piece.hasDeriv_value (p : Piece) (x : ℝ) : HasDerivAt p.value (p.slope x) x := by
  have h6 := hasDerivAt_const x ((p.c 6 : ℝ) : ℝ)
  have h5 := horner_step ((p.c 5 : ℝ)) (p.lo:ℝ) x h6
  have h4 := horner_step ((p.c 4 : ℝ)) (p.lo:ℝ) x h5
  have h3 := horner_step ((p.c 3 : ℝ)) (p.lo:ℝ) x h4
  have h2 := horner_step ((p.c 2 : ℝ)) (p.lo:ℝ) x h3
  have h1 := horner_step ((p.c 1 : ℝ)) (p.lo:ℝ) x h2
  have h0 := horner_step ((p.c 0 : ℝ)) (p.lo:ℝ) x h1
  convert h0 using 1 <;> (try simp [value,slope,slopeCoeffs,primitiveValue,intCoeffs,pad,horner]) <;> (try funext u) <;> (try simp [Piece.value,Piece.primitiveValue,Piece.intCoeffs,pad,horner]) <;> ring

theorem Piece.hasDeriv_primitive (p : Piece) (x : ℝ) : HasDerivAt p.primitiveValue (p.value x) x := by
  have h7 := hasDerivAt_const x ((p.c 6 : ℝ) / 7 : ℝ)
  have h6 := horner_step ((p.c 5 : ℝ) / 6) (p.lo:ℝ) x h7
  have h5 := horner_step ((p.c 4 : ℝ) / 5) (p.lo:ℝ) x h6
  have h4 := horner_step ((p.c 3 : ℝ) / 4) (p.lo:ℝ) x h5
  have h3 := horner_step ((p.c 2 : ℝ) / 3) (p.lo:ℝ) x h4
  have h2 := horner_step ((p.c 1 : ℝ) / 2) (p.lo:ℝ) x h3
  have h1 := horner_step ((p.c 0 : ℝ) / 1) (p.lo:ℝ) x h2
  have h0 := horner_step ((p.areaBefore:ℝ)) (p.lo:ℝ) x h1
  convert h0 using 1 <;> (try simp [value,slope,slopeCoeffs,primitiveValue,intCoeffs,pad,horner]) <;> (try funext u) <;> (try simp [Piece.value,Piece.primitiveValue,Piece.intCoeffs,pad,horner]) <;> ring

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set
noncomputable section

def rcQ : ℚ := 4356751/12500000
def zdepQ : ℚ := 783/1000
def rc : ℝ := rcQ
def zdep : ℝ := zdepQ


def Piece.slopeTest (p : Piece) (k s : ℚ) : ℚ :=
  lower [k+s*p.c 1,s*2*p.c 2,s*3*p.c 3,s*4*p.c 4,s*5*p.c 5,s*6*p.c 6] (p.hi-p.lo)

theorem Piece.slope_bound (p : Piece) (k s : ℚ) {x : ℝ} (hx : x ∈ Icc (p.lo:ℝ) p.hi) :
    (p.slopeTest k s : ℝ) ≤ (k:ℝ)+(s:ℝ)*p.slope x := by
  unfold slopeTest
  apply le_trans (lower_le_horner _ (sub_nonneg.mpr hx.1)
    (show x-(p.lo:ℝ) ≤ ((p.hi-p.lo:ℚ):ℝ) by push_cast; linarith [hx.2]))
  simp [slope,slopeCoeffs,horner]
  ring_nf
  exact le_rfl

def Piece.Valid (p : Piece) : Prop :=
  p.coeff.length≤7 ∧
  0≤p.slopeTest 0 (-1) ∧
  (p.hi≤rcQ ∧ 0≤p.slopeTest 1 1 ∧ p.qvalue p.hi≤lamQ-p.hi ∨
   p.lo=rcQ ∧ p.hi=zdepQ ∧ p.coeff=[lamQ-p.lo,-1] ∨
   zdepQ≤p.lo ∧ 0≤p.slopeTest (-1) (-1) ∧ p.qvalue p.lo≤lamQ-p.lo)

instance (p : Piece) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem Piece.antitone_score (p : Piece) (h : p.Valid) : AntitoneOn p.value (Icc (p.lo:ℝ) p.hi) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=p.slope) (convex_Icc _ _) p.continuous_value.continuousOn
    (fun x _ => (p.hasDeriv_value x).hasDerivWithinAt)
  intro x hx
  have h' := p.slope_bound 0 (-1) (interior_subset hx)
  have ha : (0:ℝ)≤p.slopeTest 0 (-1) := by exact_mod_cast h.2.1
  norm_num at h'
  linarith

theorem Piece.antitone_score_add (p : Piece) (h : 0≤p.slopeTest (-1) (-1)) :
    AntitoneOn (fun x => p.value x + x) (Icc (p.lo:ℝ) p.hi) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=fun x => p.slope x + 1) (convex_Icc _ _)
    (p.continuous_value.add continuous_id).continuousOn
    (fun x _ => ((p.hasDeriv_value x).add (hasDerivAt_id x)).hasDerivWithinAt)
  intro x hx
  have h' := p.slope_bound (-1) (-1) (interior_subset hx)
  have ha : (0:ℝ)≤p.slopeTest (-1) (-1) := by exact_mod_cast h
  norm_num at h'
  linarith

theorem Piece.monotone_score_add (p : Piece) (h : 0≤p.slopeTest 1 1) :
    MonotoneOn (fun x => p.value x + x) (Icc (p.lo:ℝ) p.hi) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f':=fun x => p.slope x + 1) (convex_Icc _ _)
    (p.continuous_value.add continuous_id).continuousOn
    (fun x _ => ((p.hasDeriv_value x).add (hasDerivAt_id x)).hasDerivWithinAt)
  intro x hx
  have h' := p.slope_bound 1 1 (interior_subset hx)
  have ha : (0:ℝ)≤p.slopeTest 1 1 := by exact_mod_cast h
  norm_num at h'
  linarith

theorem Piece.linear_value (p : Piece) (h : p.coeff=[lamQ-p.lo,-1]) (x : ℝ) :
    p.value x=lam-x := by
  simp [value,pad,horner,c,h,lam]

theorem Piece.ceiling (p : Piece) (h : p.Valid) {x : ℝ} (hx : x∈Icc (p.lo:ℝ) p.hi) :
    p.value x ≤ lam-x := by
  rcases h.2.2 with ⟨_,hd,he⟩|⟨_,_,hh⟩|⟨_,hd,he⟩
  · have hh := p.monotone_score_add hd hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2
    have he' : (p.qvalue p.hi:ℝ)≤lam-(p.hi:ℝ) := by unfold lam; exact_mod_cast he
    rw [p.cast_qvalue] at he'
    linarith
  · exact (p.linear_value hh x).le
  · have hh := p.antitone_score_add hd ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
    have he' : (p.qvalue p.lo:ℝ)≤lam-(p.lo:ℝ) := by unfold lam; exact_mod_cast he
    rw [p.cast_qvalue] at he'
    linarith

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
noncomputable section


def Piece.first (p : Piece) : Knot := ⟨p.lo,p.qvalue p.lo,p.qprimitive p.lo⟩
def Piece.last (p : Piece) : Knot := ⟨p.hi,p.qvalue p.hi,p.qprimitive p.hi⟩

def Chain (a : Knot) : List Piece → Knot → Prop
  | [], b => a=b
  | p::ps, b => p.first=a ∧ p.lo < p.hi ∧ Chain p.last ps b

instance chainDecidable (a : Knot) (ps : List Piece) (b : Knot) : Decidable (Chain a ps b) := by
  cases ps with
  | nil => exact inferInstanceAs (Decidable (a=b))
  | cons p ps =>
    letI := chainDecidable p.last ps b
    exact inferInstanceAs (Decidable (p.first=a ∧ p.lo < p.hi ∧ Chain p.last ps b))

theorem Chain.append {a b c : Knot} {ps qs : List Piece} (h : Chain a ps b) (k : Chain b qs c) :
    Chain a (ps++qs) c := by
  induction ps generalizing a with
  | nil => cases (show a=b from h); exact k
  | cons p ps ih =>
    rcases h with ⟨rfl,ho,hh⟩
    exact ⟨rfl,ho,ih hh⟩

theorem Chain.le {ps : List Piece} {a b : Knot} (h : Chain a ps b) : a.x ≤ b.x := by
  induction ps generalizing a with
  | nil => exact le_of_eq (congrArg Knot.x h)
  | cons p ps ih =>
    rcases h with ⟨rfl,ho,h⟩
    exact ho.le.trans (ih h)

theorem select_start {ps : List Piece} {a b : Knot} (h : Chain a ps b)
    (v : Piece → ℝ → ℝ) (asKnot : Knot → ℚ)
    (hs : ∀ p, v p p.lo = (asKnot p.first : ℝ)) :
    select v (asKnot b) ps a.x = asKnot a := by
  cases ps with
  | nil => cases (show a=b from h); rfl
  | cons p ps =>
    rcases h with ⟨rfl,ho,_⟩
    simpa [select,Piece.first,show (p.lo:ℝ) ≤ p.hi by exact_mod_cast ho.le] using hs p

theorem select_right {ps : List Piece} {b : Knot} (p : Piece) (h : Chain p.last ps b)
    (v : Piece → ℝ → ℝ) (asKnot : Knot → ℚ)
    (hs : ∀ p, v p p.lo = (asKnot p.first : ℝ))
    (he : ∀ p, v p p.hi = (asKnot p.last : ℝ))
    {x : ℝ} (hx : (p.hi : ℝ) ≤ x) :
    select v (asKnot b) (p::ps) x = select v (asKnot b) ps x := by
  rcases hx.eq_or_lt with rfl|hx
  · rw [select,if_pos le_rfl,he,← select_start h v asKnot hs]; rfl
  · rw [select,if_neg hx.not_ge]

theorem select_mem {ps : List Piece} {a b : Knot} (h : Chain a ps b)
    (v : Piece → ℝ → ℝ) (asKnot : Knot → ℚ)
    (hs : ∀ p, v p p.lo = (asKnot p.first : ℝ))
    (he : ∀ p, v p p.hi = (asKnot p.last : ℝ)) {p : Piece} (hp : p ∈ ps)
    {x : ℝ} (hx : x ∈ Icc (p.lo:ℝ) p.hi) :
    select v (asKnot b) ps x = v p x := by
  induction ps generalizing a with
  | nil => cases hp
  | cons q qs ih =>
    rcases h with ⟨rfl,_,hc⟩
    rcases List.mem_cons.mp hp with rfl|hp
    · exact if_pos hx.2
    · have after : (q.hi:ℚ) ≤ p.lo := by
        have ordered {u v : Knot} {l : List Piece} (ch : Chain u l v)
            (m : p ∈ l) : u.x ≤ p.lo := by
          induction l generalizing u with
          | nil => cases m
          | cons row rest ih =>
            rcases ch with ⟨rfl,hlt,ch⟩
            rcases List.mem_cons.mp m with rfl|m
            · exact le_rfl
            · exact hlt.le.trans (ih ch m)
        exact ordered hc hp
      rw [select_right q hc v asKnot hs he ((by exact_mod_cast after : (q.hi:ℝ) ≤ p.lo).trans hx.1)]
      exact ih hc hp

theorem select_end {ps : List Piece} {a b : Knot} (h : Chain a ps b)
    (v : Piece → ℝ → ℝ) (asKnot : Knot → ℚ)
    (hs : ∀ p, v p p.lo = (asKnot p.first : ℝ)) (he : ∀ p, v p p.hi = (asKnot p.last : ℝ)) :
    select v (asKnot b) ps b.x = (asKnot b : ℝ) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨_,_,hc⟩ := h
    rw [select_right p hc v asKnot hs he (by exact_mod_cast hc.le)]
    exact ih hc

theorem start_value (p : Piece) : p.value p.lo=(p.first.y:ℝ) := (p.cast_qvalue _).symm
theorem end_value (p : Piece) : p.value p.hi=(p.last.y:ℝ) := (p.cast_qvalue _).symm
theorem start_primitive (p : Piece) : p.primitiveValue p.lo=(p.first.j:ℝ) := (p.cast_qprimitive _).symm
theorem end_primitive (p : Piece) : p.primitiveValue p.hi=(p.last.j:ℝ) := (p.cast_qprimitive _).symm

theorem Chain.select_end_score {ps : List Piece} {a b : Knot} (h : Chain a ps b) :
    scoreEval b ps b.x = (b.y:ℝ) := select_end h _ Knot.y start_value end_value
theorem Chain.select_end_primitive {ps : List Piece} {a b : Knot} (h : Chain a ps b) :
    primitiveEval b ps b.x = (b.j:ℝ) := select_end h _ Knot.j start_primitive end_primitive
end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Set
noncomputable section


def ratio (lam : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := (lam-x)/φ x


def lowSecond (lam : ℝ) (φ : ℝ → ℝ) (β a b p q x : ℝ) : ℝ :=
  q + β * KP φ p q x + correction lam φ a b x

def highFirst (lam : ℝ) (φ : ℝ → ℝ) (β a b p q r : ℝ) : ℝ :=
  q + β * deltaP φ p q + potential lam φ r q - lam -
    max (-φ q) 0 * max (a*r+b) 0


theorem affine_parameter {lo hi x : ℝ} (hx : x ∈ Icc lo hi) :
    ∃ u ∈ Icc (0:ℝ) 1, x = lo + u * (hi-lo) := by
  rcases eq_or_lt_of_le (hx.1.trans hx.2) with h|h
  · exact ⟨0, ⟨le_rfl,zero_le_one⟩, by simpa using le_antisymm (hx.2.trans h.ge) hx.1⟩
  · have hp : 0 < hi-lo := sub_pos.mpr h
    refine ⟨(x-lo)/(hi-lo), ⟨div_nonneg (sub_nonneg.mpr hx.1) hp.le, (div_le_one hp).mpr (by linarith [hx.2])⟩, ?_⟩
    rw [div_mul_cancel₀ _ hp.ne']; ring

private theorem scaled (lam : ℝ) (φ : ℝ → ℝ) (a b x : ℝ) (h : 0 < φ x) :
    φ x * max (a * ratio lam φ x + b) 0 = correction lam φ a b x := by
  have hc : φ x * (a * ratio lam φ x + b) = a * (lam-x) + b * φ x := by
    unfold ratio
    field_simp
  simp only [mul_max_of_nonneg _ _ h.le, mul_zero, hc, correction]


structure CubeBounds (lam rc : ℝ) (φ : ℝ → ℝ) (β a b p : ℝ) : Prop where
  L1 : ∀ u ∈ Icc (0:ℝ) 1, ∀ w ∈ Icc (0:ℝ) 1,
    let q := u * min p lam
    lowFirst lam φ β a b p q (q+w*(lam-q)) ≤ 0
  L2 : p ≤ lam → ∀ u ∈ Icc (0:ℝ) 1, ∀ w ∈ Icc (0:ℝ) 1,
    lowSecond lam φ β a b p (u*p) (p+w*(lam-p)) ≤ 0
  L3 : ∀ u ∈ Icc (0:ℝ) 1, ∀ w ∈ Icc (0:ℝ) 1,
    highFirst lam φ β a b p (u*p) (ratio lam φ (w*rc)) ≤ 0
  L3id : ∀ u ∈ Icc (0:ℝ) 1, highFirst lam φ β a b p (u*p) 1 ≤ 0
  L4 : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, ∀ w ∈ Icc (0:ℝ) 1,
    highSecond lam φ β a b p (u*p) (p+v*(1-p)) (ratio lam φ (w*rc)) ≤ 0
  L4id : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
    highSecond lam φ β a b p (u*p) (p+v*(1-p)) 1 ≤ 0


theorem cubes_imply_eq37_eq38 {lam rc p : ℝ} {φ β a b : ℝ → ℝ}
    (hpos : ∀ x ∈ Ico (0:ℝ) lam, 0 < φ x)
    (hid : ∀ x ∈ Icc rc lam, φ x = lam-x) (h : CubeBounds lam rc φ (β p) (a p) (b p) p) :
    Eq37 lam φ β (fun s => correction lam φ (a s) (b s)) p ∧
    Eq38 lam φ β (fun s => correction lam φ (a s) (b s)) p := by
  constructor
  · intro x hx
    constructor
    · intro q hq hqpx
      have hp := (le_min_iff.mp hqpx).1
      have hqx := (le_min_iff.mp hqpx).2
      obtain ⟨u,hu,eu⟩ := affine_parameter (lo:=0) (hi:=min p lam) (x:=q)
        ⟨hq,le_min hp (hqx.trans hx.2.le)⟩
      obtain ⟨w,hw,ew⟩ := affine_parameter (lo:=q) (hi:=lam) (x:=x) ⟨hqx,hx.2.le⟩
      simp only [sub_zero, zero_add] at eu
      have hh := h.L1 u hu w hw
      dsimp only at hh
      rw [← eu, ← ew] at hh
      exact sub_nonpos.mp hh
    · intro q hq hqp hpx
      obtain ⟨u,hu,eu⟩ := affine_parameter (lo:=0) (hi:=p) (x:=q) ⟨hq,hqp⟩
      obtain ⟨w,hw,ew⟩ := affine_parameter (lo:=p) (hi:=lam) (x:=x) ⟨hpx,hx.2.le⟩
      simp only [sub_zero,zero_add] at eu
      simpa only [← eu, ← ew,lowSecond] using h.L2 (hpx.trans hx.2.le) u hu w hw
  · intro x hx
    have hs := scaled lam φ (a p) (b p) x (hpos x hx)
    have hr : ∀ (F : ℝ → Prop), (∀ w ∈ Icc (0:ℝ) 1, F (ratio lam φ (w*rc))) →
        F 1 → F (ratio lam φ x) := by
      intro F ha hb
      by_cases hl : x ≤ rc
      · obtain ⟨w,hw,ew⟩ := affine_parameter (lo:=0) (hi:=rc) (x:=x) ⟨hx.1,hl⟩
        simp only [zero_add,sub_zero] at ew
        simpa only [← ew] using ha w hw
      · have he : ratio lam φ x = 1 := by
          rw [ratio,hid x ⟨le_of_not_ge hl,hx.2.le⟩,div_self (sub_pos.mpr hx.2).ne']
        simpa only [he] using hb
    have clear (v t : ℝ) (hv : v - t * max (a p * ratio lam φ x + b p) 0 ≤ 0) :
        φ x * v ≤ t * correction lam φ (a p) (b p) x := by
      calc
        _ ≤ φ x * (t * max (a p * ratio lam φ x + b p) 0) :=
          mul_le_mul_of_nonneg_left (sub_nonpos.mp hv) (hpos x hx).le
        _ = _ := by rw [← hs]; ring
    constructor
    · intro q hq hqp
      obtain ⟨u,hu,eu⟩ := affine_parameter (lo:=0) (hi:=p) (x:=q) ⟨hq,hqp⟩
      simp only [sub_zero,zero_add] at eu
      apply clear
      apply hr (fun r => highFirst lam φ (β p) (a p) (b p) p q r ≤ 0)
      · intro w hw; simpa only [← eu] using h.L3 u hu w hw
      · simpa only [← eu] using h.L3id u hu
    · intro q z hq hqp hpz hz
      obtain ⟨u,hu,eu⟩ := affine_parameter (lo:=0) (hi:=p) (x:=q) ⟨hq,hqp⟩
      obtain ⟨v,hv,ev⟩ := affine_parameter (lo:=p) (hi:=1) (x:=z) ⟨hpz,hz⟩
      simp only [sub_zero,zero_add] at eu
      apply clear
      apply hr (fun r => highSecond lam φ (β p) (a p) (b p) p q z r ≤ 0)
      · intro w hw; simpa only [← eu, ← ev] using h.L4 u hu v hv w hw
      · simpa only [← eu, ← ev] using h.L4id u hu v hv

end
end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open Set PaperCurve PaperBox


def ratioNumerator (p : Piece) : List ℚ := pad (fun k =>
  (1-(k:ℚ))*p.c k + (lamQ-p.lo)*((k:ℚ)+1)*p.c (k+1))

def validatesRatio (p : Piece) : Prop := p.lo<lamQ → 0 ≤ lower (ratioNumerator p) (p.hi-p.lo)
instance (p : Piece) : Decidable (validatesRatio p) := inferInstanceAs (Decidable (_ → _))

theorem ratioNumerator_nonneg (p : Piece) (hn : p.coeff.length ≤ 7) (h : validatesRatio p)
    {x : ℝ} (hx : x∈Icc (p.lo:ℝ) p.hi) (hl : x<lam) :
    0 ≤ p.value x+(lam-x)*p.slope x := by
  have h₁ : p.lo<lamQ := by exact_mod_cast (hx.1.trans_lt hl : (p.lo:ℝ)<(lamQ:ℝ))
  have h₂ : (0:ℝ) ≤ (lower (ratioNumerator p) (p.hi-p.lo):ℝ) := by exact_mod_cast h h₁
  have hh := lower_le_horner (ratioNumerator p) (sub_nonneg.mpr hx.1)
    (show x-(p.lo:ℝ) ≤ ((p.hi-p.lo:ℚ):ℝ) by push_cast;linarith [hx.2])
  have h₇ : p.c 7=0 := by simp [Piece.c,List.getElem?_eq_none hn]
  apply h₂.trans (hh.trans _)
  unfold ratioNumerator Piece.value Piece.slope Piece.slopeCoeffs pad horner lam
  simp [h₇,List.foldr] <;> push_cast <;> ring_nf <;> rfl


theorem antitone_rows {ps : List Piece} {a b : Knot} (chain : Chain a ps b)
    {f : ℝ → ℝ} {x y : ℝ} (hx : (a.x:ℝ) ≤ x) (hy : y ≤ (b.x:ℝ)) (hxy : x ≤ y)
    (hf : ∀ r∈ps,∀ s t : ℝ,(r.lo:ℝ) ≤ s → s ≤ t → t ≤ r.hi → x ≤ s → t ≤ y → f t ≤ f s) : f y ≤ f x := by
  induction ps generalizing a x y with
  | nil => rw [show a=b from chain] at hx;rw [show x=y by linarith]
  | cons r ps ih =>
    obtain ⟨rfl,_,ch⟩ := chain
    change (r.lo:ℝ) ≤ x at hx
    by_cases h : y ≤ r.hi
    · exact hf r (by simp) x y hx hxy h le_rfl le_rfl
    have tail (u : ℝ) (hr : r.hi ≤ u) (hxu : x ≤ u) (huy : u ≤ y) : f y ≤ f u := by
      apply ih ch hr hy huy
      intro row hm s t hrs st hts hus hty
      exact hf row (by simp [hm]) s t hrs st hts (hxu.trans hus) hty
    by_cases ha : r.hi ≤ x
    · exact tail x ha le_rfl hxy
    · exact (tail r.hi le_rfl (le_of_not_ge ha) (le_of_not_ge h)).trans
        (hf r (by simp) x r.hi hx (le_of_not_ge ha) le_rfl le_rfl (le_of_not_ge h))


theorem ratio_row {p : Piece} (hn : p.coeff.length ≤ 7) (h : validatesRatio p)
    {s t : ℝ} (hs : (p.lo:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ p.hi) (hl : t<lam)
    (positive : ∀ x∈Icc s t,0<p.value x) : ratio lam p.value t ≤ ratio lam p.value s := by
  have hd (x : ℝ) (hx : x∈Icc s t) : HasDerivAt (ratio lam p.value)
      (((-1)*p.value x-(lam-x)*p.slope x)/(p.value x)^2) x := by
    have hi := ((hasDerivAt_const x lam).sub (hasDerivAt_id x)).div (p.hasDeriv_value x) (positive x hx).ne'
    change HasDerivAt (fun z : ℝ => (lam-z)/p.value z) _ x
    simpa [Pi.div_def,Pi.sub_def] using hi
  apply antitoneOn_of_hasDerivWithinAt_nonpos (D:=Icc s t) (f':=fun x => _) (convex_Icc _ _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) _
    (show s∈Icc s t from ⟨le_rfl,hst⟩) (show t∈Icc s t from ⟨hst,le_rfl⟩) hst
  intro x hx
  have hI := interior_subset hx
  have hh := ratioNumerator_nonneg p hn h ⟨hs.trans hI.1,hI.2.trans ht⟩ (hI.2.trans_lt hl)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000



def centralPiece : Piece := rows30[4]!
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open PaperCurve
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 100000000

private theorem checkRatio00 : rows00.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio01 : rows01.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio02 : rows02.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio03 : rows03.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio04 : rows04.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio05 : rows05.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio06 : rows06.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio07 : rows07.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio08 : rows08.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio09 : rows09.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio10 : rows10.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio11 : rows11.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio12 : rows12.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio13 : rows13.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio14 : rows14.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio15 : rows15.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio16 : rows16.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio17 : rows17.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio18 : rows18.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio19 : rows19.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio20 : rows20.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio21 : rows21.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio22 : rows22.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio23 : rows23.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio24 : rows24.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio25 : rows25.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio26 : rows26.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio27 : rows27.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio28 : rows28.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio29 : rows29.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio30 : rows30.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio31 : rows31.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio32 : rows32.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio33 : rows33.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio34 : rows34.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio35 : rows35.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio36 : rows36.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio37 : rows37.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio38 : rows38.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio39 : rows39.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio40 : rows40.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio41 : rows41.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio42 : rows42.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio43 : rows43.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio44 : rows44.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio45 : rows45.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio46 : rows46.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio47 : rows47.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio48 : rows48.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio49 : rows49.all (fun p => decide (validatesRatio p))=true := by decide +kernel
private theorem checkRatio50 : rows50.all (fun p => decide (validatesRatio p))=true := by decide +kernel

theorem data_ratios : ∀ p ∈ pieces, validatesRatio p := by
  have combine {x y : List Piece} (hx : ∀ p∈x,validatesRatio p) (hy : ∀ p∈y,validatesRatio p) : ∀ p∈x++y,validatesRatio p := by
    intro p hp; rcases List.mem_append.mp hp with h|h; exact hx p h; exact hy p h
  unfold pieces
  simp only [List.append_assoc]
  have v00 : ∀ p∈rows00,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio00 p hp)
  have v01 : ∀ p∈rows01,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio01 p hp)
  have v02 : ∀ p∈rows02,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio02 p hp)
  have v03 : ∀ p∈rows03,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio03 p hp)
  have v04 : ∀ p∈rows04,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio04 p hp)
  have v05 : ∀ p∈rows05,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio05 p hp)
  have v06 : ∀ p∈rows06,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio06 p hp)
  have v07 : ∀ p∈rows07,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio07 p hp)
  have v08 : ∀ p∈rows08,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio08 p hp)
  have v09 : ∀ p∈rows09,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio09 p hp)
  have v10 : ∀ p∈rows10,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio10 p hp)
  have v11 : ∀ p∈rows11,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio11 p hp)
  have v12 : ∀ p∈rows12,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio12 p hp)
  have v13 : ∀ p∈rows13,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio13 p hp)
  have v14 : ∀ p∈rows14,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio14 p hp)
  have v15 : ∀ p∈rows15,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio15 p hp)
  have v16 : ∀ p∈rows16,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio16 p hp)
  have v17 : ∀ p∈rows17,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio17 p hp)
  have v18 : ∀ p∈rows18,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio18 p hp)
  have v19 : ∀ p∈rows19,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio19 p hp)
  have v20 : ∀ p∈rows20,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio20 p hp)
  have v21 : ∀ p∈rows21,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio21 p hp)
  have v22 : ∀ p∈rows22,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio22 p hp)
  have v23 : ∀ p∈rows23,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio23 p hp)
  have v24 : ∀ p∈rows24,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio24 p hp)
  have v25 : ∀ p∈rows25,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio25 p hp)
  have v26 : ∀ p∈rows26,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio26 p hp)
  have v27 : ∀ p∈rows27,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio27 p hp)
  have v28 : ∀ p∈rows28,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio28 p hp)
  have v29 : ∀ p∈rows29,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio29 p hp)
  have v30 : ∀ p∈rows30,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio30 p hp)
  have v31 : ∀ p∈rows31,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio31 p hp)
  have v32 : ∀ p∈rows32,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio32 p hp)
  have v33 : ∀ p∈rows33,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio33 p hp)
  have v34 : ∀ p∈rows34,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio34 p hp)
  have v35 : ∀ p∈rows35,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio35 p hp)
  have v36 : ∀ p∈rows36,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio36 p hp)
  have v37 : ∀ p∈rows37,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio37 p hp)
  have v38 : ∀ p∈rows38,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio38 p hp)
  have v39 : ∀ p∈rows39,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio39 p hp)
  have v40 : ∀ p∈rows40,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio40 p hp)
  have v41 : ∀ p∈rows41,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio41 p hp)
  have v42 : ∀ p∈rows42,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio42 p hp)
  have v43 : ∀ p∈rows43,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio43 p hp)
  have v44 : ∀ p∈rows44,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio44 p hp)
  have v45 : ∀ p∈rows45,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio45 p hp)
  have v46 : ∀ p∈rows46,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio46 p hp)
  have v47 : ∀ p∈rows47,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio47 p hp)
  have v48 : ∀ p∈rows48,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio48 p hp)
  have v49 : ∀ p∈rows49,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio49 p hp)
  have v50 : ∀ p∈rows50,validatesRatio p := fun p hp => of_decide_eq_true (List.all_eq_true.mp checkRatio50 p hp)
  exact (combine (x:=rows00) v00 (combine (x:=rows01) v01 (combine (x:=rows02) v02 (combine (x:=rows03) v03 (combine (x:=rows04) v04 (combine (x:=rows05) v05 (combine (x:=rows06) v06 (combine (x:=rows07) v07 (combine (x:=rows08) v08 (combine (x:=rows09) v09 (combine (x:=rows10) v10 (combine (x:=rows11) v11 (combine (x:=rows12) v12 (combine (x:=rows13) v13 (combine (x:=rows14) v14 (combine (x:=rows15) v15 (combine (x:=rows16) v16 (combine (x:=rows17) v17 (combine (x:=rows18) v18 (combine (x:=rows19) v19 (combine (x:=rows20) v20 (combine (x:=rows21) v21 (combine (x:=rows22) v22 (combine (x:=rows23) v23 (combine (x:=rows24) v24 (combine (x:=rows25) v25 (combine (x:=rows26) v26 (combine (x:=rows27) v27 (combine (x:=rows28) v28 (combine (x:=rows29) v29 (combine (x:=rows30) v30 (combine (x:=rows31) v31 (combine (x:=rows32) v32 (combine (x:=rows33) v33 (combine (x:=rows34) v34 (combine (x:=rows35) v35 (combine (x:=rows36) v36 (combine (x:=rows37) v37 (combine (x:=rows38) v38 (combine (x:=rows39) v39 (combine (x:=rows40) v40 (combine (x:=rows41) v41 (combine (x:=rows42) v42 (combine (x:=rows43) v43 (combine (x:=rows44) v44 (combine (x:=rows45) v45 (combine (x:=rows46) v46 (combine (x:=rows47) v47 (combine (x:=rows48) v48 (combine (x:=rows49) v49 (combine (x:=rows50) v50 (by simp))))))))))))))))))))))))))))))))))))))))))))))))))))

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain00 : Chain ⟨0,(7822731457835295257/17866362234375000000),0⟩ rows00 ⟨(81515121/275000000),(2346861296600981730646813474523462624149805782772189198872235999366890627/9234819494869283429330223324328670428052414703515625000000000000000000000),(41819370185979374838877511121616731039555275531706962375858952983364615113129/418142062178415642291408364106279249970472265625000000000000000000000000000000)⟩ := by decide +kernel
theorem valid00 : rows00.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain01 : Chain ⟨(81515121/275000000),(2346861296600981730646813474523462624149805782772189198872235999366890627/9234819494869283429330223324328670428052414703515625000000000000000000000),(41819370185979374838877511121616731039555275531706962375858952983364615113129/418142062178415642291408364106279249970472265625000000000000000000000000000000)⟩ rows01 ⟨(82000999/275000000),(15567994334412130018604094101567670060905143467229993586856467730301376477/61565463299128556195534822162191136187016098023437500000000000000000000000),(414880522402574095641891548628632586125613195129632669279580739583745350773/4129798144972006343618848040555844444152812500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid01 : rows01.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain02 : Chain ⟨(82000999/275000000),(15567994334412130018604094101567670060905143467229993586856467730301376477/61565463299128556195534822162191136187016098023437500000000000000000000000),(414880522402574095641891548628632586125613195129632669279580739583745350773/4129798144972006343618848040555844444152812500000000000000000000000000000000)⟩ rows02 ⟨(7498807/25000000),(211226751330132327793462369059047824219845190552045079487390667930099927/839529044988116675393656665848060948004764973046875000000000000000000000),(2789619894897764096617934567498034785444063282259881114911845595838035840927/27645756177085331721746007544216809915403125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid02 : rows02.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain03 : Chain ⟨(7498807/25000000),(211226751330132327793462369059047824219845190552045079487390667930099927/839529044988116675393656665848060948004764973046875000000000000000000000),(2789619894897764096617934567498034785444063282259881114911845595838035840927/27645756177085331721746007544216809915403125000000000000000000000000000000000)⟩ rows03 ⟨(16594551/55000000),(46234959242101206772041375299221449295517440031347848855571935154932737519/184696389897385668586604466486573408561048294070312500000000000000000000000),(169513643484719539214439190070257802270591743381311489560388991921891239101081/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid03 : rows03.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain04 : Chain ⟨(16594551/55000000),(46234959242101206772041375299221449295517440031347848855571935154932737519/184696389897385668586604466486573408561048294070312500000000000000000000000),(169513643484719539214439190070257802270591743381311489560388991921891239101081/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ rows04 ⟨(83458633/275000000),(7666538430930750485465636869217310283902902226997956646931219134514702873/30782731649564278097767411081095568093508049011718750000000000000000000000),(37833670679248604725950960675930629915646848853701638376548264791512615268889/371681833047480570925696323650025999973753125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid04 : rows04.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain05 : Chain ⟨(83458633/275000000),(7666538430930750485465636869217310283902902226997956646931219134514702873/30782731649564278097767411081095568093508049011718750000000000000000000000),(37833670679248604725950960675930629915646848853701638376548264791512615268889/371681833047480570925696323650025999973753125000000000000000000000000000000000)⟩ rows05 ⟨(83944511/275000000),(45762724370706242744832936927861176564742931528083352922318827524377969497/184696389897385668586604466486573408561048294070312500000000000000000000000),(170985614716597329192589968236977963608856201584362322139526232535861320766553/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid05 : rows05.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain06 : Chain ⟨(83944511/275000000),(45762724370706242744832936927861176564742931528083352922318827524377969497/184696389897385668586604466486573408561048294070312500000000000000000000000),(170985614716597329192589968236977963608856201584362322139526232535861320766553/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ rows06 ⟨(84430389/275000000),(45525311343396514747014100024996780009617550564396847621538976728036973673/184696389897385668586604466486573408561048294070312500000000000000000000000),(171715920607205525615286112283165290287621845658913320782354636831750050530869/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid06 : rows06.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain07 : Chain ⟨(84430389/275000000),(45525311343396514747014100024996780009617550564396847621538976728036973673/184696389897385668586604466486573408561048294070312500000000000000000000000),(171715920607205525615286112283165290287621845658913320782354636831750050530869/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ rows07 ⟨(84916267/275000000),(503184725743547657119888543742264731002671948856351204819324848224989433/2052182109970951873184494072073037872900536600781250000000000000000000000),(114961611881832169454563419937661462556904763384511566772738878312683728370237/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid07 : rows07.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain08 : Chain ⟨(84916267/275000000),(503184725743547657119888543742264731002671948856351204819324848224989433/2052182109970951873184494072073037872900536600781250000000000000000000000),(114961611881832169454563419937661462556904763384511566772738878312683728370237/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ rows08 ⟨(17080429/55000000),(22523323178943282599553692030482342356257081767237426005525040817875647671/92348194948692834293302233243286704280524147035156250000000000000000000000),(13853206857792628934194087026683591438779730891739614874708191655143088145453/133805459897093005533250676514009359990551125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid08 : rows08.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain09 : Chain ⟨(17080429/55000000),(22523323178943282599553692030482342356257081767237426005525040817875647671/92348194948692834293302233243286704280524147035156250000000000000000000000),(13853206857792628934194087026683591438779730891739614874708191655143088145453/133805459897093005533250676514009359990551125000000000000000000000000000000000)⟩ rows09 ⟨(85888023/275000000),(2240268526079926895945536924549850193393935736257114657159215851145733617/9234819494869283429330223324328670428052414703515625000000000000000000000),(347767807177597016255098596109273125045566273792291340709706957366368710911503/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid09 : rows09.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain10 : Chain ⟨(85888023/275000000),(2240268526079926895945536924549850193393935736257114657159215851145733617/9234819494869283429330223324328670428052414703515625000000000000000000000),(347767807177597016255098596109273125045566273792291340709706957366368710911503/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows10 ⟨(86373901/275000000),(7427132569693363229858422759258923314200150108797215873173207202573776157/30782731649564278097767411081095568093508049011718750000000000000000000000),(116399233766171601890167748931453064589701163877117522085615831941769381227709/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid10 : rows10.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain11 : Chain ⟨(86373901/275000000),(7427132569693363229858422759258923314200150108797215873173207202573776157/30782731649564278097767411081095568093508049011718750000000000000000000000),(116399233766171601890167748931453064589701163877117522085615831941769381227709/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ rows11 ⟨(86859779/275000000),(44318863523585794602794991409392485377605551276490700568439813508037118913/184696389897385668586604466486573408561048294070312500000000000000000000000),(175309905920354232733621104700564090013319624204223677208343156677876373083979/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid11 : rows11.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain12 : Chain ⟨(86859779/275000000),(44318863523585794602794991409392485377605551276490700568439813508037118913/184696389897385668586604466486573408561048294070312500000000000000000000000),(175309905920354232733621104700564090013319624204223677208343156677876373083979/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ rows12 ⟨(87345657/275000000),(11018331735219819659075304868112189581026540833291659602462241464490743827/46174097474346417146651116621643352140262073517578125000000000000000000000),(352034091492762100729986917496893605793822020022721616833193603136963407638247/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid12 : rows12.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain13 : Chain ⟨(87345657/275000000),(11018331735219819659075304868112189581026540833291659602462241464490743827/46174097474346417146651116621643352140262073517578125000000000000000000000),(352034091492762100729986917496893605793822020022721616833193603136963407638247/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows13 ⟨(1596937/5000000),(83004288078561358475692364172466535293743104543100591315705672724781857/349803768745048614747356944103358728335318738769531250000000000000000000),(54092514292449569663135212250461563172971991674013428882687093230632411187/511958447723802439291592732300311294729687500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid13 : rows13.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain14 : Chain ⟨(1596937/5000000),(83004288078561358475692364172466535293743104543100591315705672724781857/349803768745048614747356944103358728335318738769531250000000000000000000),(54092514292449569663135212250461563172971991674013428882687093230632411187/511958447723802439291592732300311294729687500000000000000000000000000000000)⟩ rows14 ⟨(88317413/275000000),(43577809929543427574709527172059913788426235437748207903601171263327041221/184696389897385668586604466486573408561048294070312500000000000000000000000),(44354869784342201915908806869724101355154606806426777188609006250746529490931/418142062178415642291408364106279249970472265625000000000000000000000000000000)⟩ := by decide +kernel
theorem valid14 : rows14.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain15 : Chain ⟨(88317413/275000000),(43577809929543427574709527172059913788426235437748207903601171263327041221/184696389897385668586604466486573408561048294070312500000000000000000000000),(44354869784342201915908806869724101355154606806426777188609006250746529490931/418142062178415642291408364106279249970472265625000000000000000000000000000000)⟩ rows15 ⟨(88803291/275000000),(43327158568773956895027310191692449709459756119405202612668008012825284273/184696389897385668586604466486573408561048294070312500000000000000000000000),(356229444115398671144710921258998327411079966871721445608945927002551738304899/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid15 : rows15.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain16 : Chain ⟨(88803291/275000000),(43327158568773956895027310191692449709459756119405202612668008012825284273/184696389897385668586604466486573408561048294070312500000000000000000000000),(356229444115398671144710921258998327411079966871721445608945927002551738304899/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows16 ⟨(89289169/275000000),(897387712007987406990498158842495773020925779504767052139880513116261979/3847841456195534762220926385136946011688506126464843750000000000000000000),(3311221062490218823702354308705214236848749035867752932552224308454988720499/30973486087290047577141360304168833331146093750000000000000000000000000000000)⟩ := by decide +kernel
theorem valid16 : rows16.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain17 : Chain ⟨(89289169/275000000),(897387712007987406990498158842495773020925779504767052139880513116261979/3847841456195534762220926385136946011688506126464843750000000000000000000),(3311221062490218823702354308705214236848749035867752932552224308454988720499/30973486087290047577141360304168833331146093750000000000000000000000000000000)⟩ rows17 ⟨(89775047/275000000),(42821428521607864075657870996294678116425393025467172877734255040753759981/184696389897385668586604466486573408561048294070312500000000000000000000000),(11218319152179328954367212327998286326641488946738437806451762382437053907997/104535515544603910572852091026569812492618066406250000000000000000000000000000)⟩ := by decide +kernel
theorem valid17 : rows17.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain18 : Chain ⟨(89775047/275000000),(42821428521607864075657870996294678116425393025467172877734255040753759981/184696389897385668586604466486573408561048294070312500000000000000000000000),(11218319152179328954367212327998286326641488946738437806451762382437053907997/104535515544603910572852091026569812492618066406250000000000000000000000000000)⟩ rows18 ⟨(3610437/11000000),(42567696585970842509369670881929687898582341905938728560060095076198796241/184696389897385668586604466486573408561048294070312500000000000000000000000),(72070488061040827322821595052926141298143851826162472300848351045518484914223/669027299485465027666253382570046799952755625000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid18 : rows18.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain19 : Chain ⟨(3610437/11000000),(42567696585970842509369670881929687898582341905938728560060095076198796241/184696389897385668586604466486573408561048294070312500000000000000000000000),(72070488061040827322821595052926141298143851826162472300848351045518484914223/669027299485465027666253382570046799952755625000000000000000000000000000000000)⟩ rows19 ⟨(90746803/275000000),(37214986006336662499336154276530969757078456554241757444310853444687621/162441855670523894975025915995227272261256195312500000000000000000000000),(24114035989716835737916808626020586533610240580595030648051952422350955294067/223009099828488342555417794190015599984251875000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid19 : rows19.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain20 : Chain ⟨(90746803/275000000),(37214986006336662499336154276530969757078456554241757444310853444687621/162441855670523894975025915995227272261256195312500000000000000000000000),(24114035989716835737916808626020586533610240580595030648051952422350955294067/223009099828488342555417794190015599984251875000000000000000000000000000000000)⟩ rows20 ⟨(91232681/275000000),(21029339677103759584682447824516146204566978758940086202137404879035302019/92348194948692834293302233243286704280524147035156250000000000000000000000),(363060495050164298908870534739738706873618547903827815671283613154810273472311/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid20 : rows20.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain21 : Chain ⟨(91232681/275000000),(21029339677103759584682447824516146204566978758940086202137404879035302019/92348194948692834293302233243286704280524147035156250000000000000000000000),(363060495050164298908870534739738706873618547903827815671283613154810273472311/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows21 ⟨(91718559/275000000),(20901719709348434507057143693422571134713299102130915463966183058459621927/92348194948692834293302233243286704280524147035156250000000000000000000000),(91100572550676389232730086867499935813493784783919177907750428671058687741973/836284124356831284582816728212558499940944531250000000000000000000000000000000)⟩ := by decide +kernel
theorem valid21 : rows21.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain22 : Chain ⟨(91718559/275000000),(20901719709348434507057143693422571134713299102130915463966183058459621927/92348194948692834293302233243286704280524147035156250000000000000000000000),(91100572550676389232730086867499935813493784783919177907750428671058687741973/836284124356831284582816728212558499940944531250000000000000000000000000000000)⟩ rows22 ⟨(92204437/275000000),(6924623410823772036947907476739308507584875416199625948487572818120141317/30782731649564278097767411081095568093508049011718750000000000000000000000),(121911970091654536073280063396949013855940091714131307757668521701785189538851/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid22 : rows22.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain23 : Chain ⟨(92204437/275000000),(6924623410823772036947907476739308507584875416199625948487572818120141317/30782731649564278097767411081095568093508049011718750000000000000000000000),(121911970091654536073280063396949013855940091714131307757668521701785189538851/1115045499142441712777088970950077999921259375000000000000000000000000000000000)⟩ rows23 ⟨(18538063/55000000),(10322717821580035029344674613397325690424414845375045910131298841808275229/46174097474346417146651116621643352140262073517578125000000000000000000000),(367061337030655382408499590442904491854764489664746499826471631293323075349067/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid23 : rows23.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain24 : Chain ⟨(18538063/55000000),(10322717821580035029344674613397325690424414845375045910131298841808275229/46174097474346417146651116621643352140262073517578125000000000000000000000),(367061337030655382408499590442904491854764489664746499826471631293323075349067/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows24 ⟨(8470563/25000000),(372987788285004949444367127139254600754804870033286053618806260421634717/1679058089976233350787313331696121896009529946093750000000000000000000000),(1522225061795862151817390929839717827039351477638889828311899279014029351451/13822878088542665860873003772108404957701562500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid24 : rows24.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain25 : Chain ⟨(8470563/25000000),(372987788285004949444367127139254600754804870033286053618806260421634717/1679058089976233350787313331696121896009529946093750000000000000000000000),(1522225061795862151817390929839717827039351477638889828311899279014029351451/13822878088542665860873003772108404957701562500000000000000000000000000000000)⟩ rows25 ⟨(93662071/275000000),(2264494986877994210534372095785747317850961570718185885867165474256641669/10260910549854759365922470360365189364502683003906250000000000000000000000),(57050480259291040427819386636790374522294310964532533327734060148471101099/516224768121500792952356005069480555519101562500000000000000000000000000000)⟩ := by decide +kernel
theorem valid25 : rows25.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain26 : Chain ⟨(93662071/275000000),(2264494986877994210534372095785747317850961570718185885867165474256641669/10260910549854759365922470360365189364502683003906250000000000000000000000),(57050480259291040427819386636790374522294310964532533327734060148471101099/516224768121500792952356005069480555519101562500000000000000000000000000000)⟩ rows26 ⟨(94147949/275000000),(10122029811062038535358112138837696629427470639194732144280562553168662309/46174097474346417146651116621643352140262073517578125000000000000000000000),(185493554703410544456864968620395789457663114683258911337860415554825801376341/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ := by decide +kernel
theorem valid26 : rows26.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain27 : Chain ⟨(94147949/275000000),(10122029811062038535358112138837696629427470639194732144280562553168662309/46174097474346417146651116621643352140262073517578125000000000000000000000),(185493554703410544456864968620395789457663114683258911337860415554825801376341/1672568248713662569165633456425116999881889062500000000000000000000000000000000)⟩ rows27 ⟨(94633827/275000000),(40210701864500751380484499970671002930602809239515043968819431225428093587/184696389897385668586604466486573408561048294070312500000000000000000000000),(23267393898698077766845190853794104028610237345850944461342402631087678854677/209071031089207821145704182053139624985236132812500000000000000000000000000000)⟩ := by decide +kernel
theorem valid27 : rows27.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain28 : Chain ⟨(94633827/275000000),(40210701864500751380484499970671002930602809239515043968819431225428093587/184696389897385668586604466486573408561048294070312500000000000000000000000),(23267393898698077766845190853794104028610237345850944461342402631087678854677/209071031089207821145704182053139624985236132812500000000000000000000000000000)⟩ rows28 ⟨(19023941/55000000),(98590163649705876538350705556618526711968898573593182083286961122360329/456040468882433749596554238238452860644563689062500000000000000000000000),(3113004573461192622111821076795746455606511135892254027741798499764689948099/27876137478561042819427224273751949998031484375000000000000000000000000000000)⟩ := by decide +kernel
theorem valid28 : rows28.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain29 : Chain ⟨(19023941/55000000),(98590163649705876538350705556618526711968898573593182083286961122360329/456040468882433749596554238238452860644563689062500000000000000000000000),(3113004573461192622111821076795746455606511135892254027741798499764689948099/27876137478561042819427224273751949998031484375000000000000000000000000000000)⟩ rows29 ⟨(95605583/275000000),(39643373805030105917205527544012174775455701296975068744135550115134849309/184696389897385668586604466486573408561048294070312500000000000000000000000),(374833717227974526408446235390156784451302951271794638477109628470543599512101/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ := by decide +kernel
theorem valid29 : rows29.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain30 : Chain ⟨(95605583/275000000),(39643373805030105917205527544012174775455701296975068744135550115134849309/184696389897385668586604466486573408561048294070312500000000000000000000000),(374833717227974526408446235390156784451302951271794638477109628470543599512101/3345136497427325138331266912850233999763778125000000000000000000000000000000000)⟩ rows30 ⟨(1569/2000),(-1113294675039/5000000000000),(1104460757034187/10000000000000000)⟩ := by decide +kernel
theorem valid30 : rows30.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain31 : Chain ⟨(1569/2000),(-1113294675039/5000000000000),(1104460757034187/10000000000000000)⟩ rows31 ⟨(1577/2000),(-2284943736527/10000000000000),(4381751884513627/40000000000000000)⟩ := by decide +kernel
theorem valid31 : rows31.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain32 : Chain ⟨(1577/2000),(-2284943736527/10000000000000),(4381751884513627/40000000000000000)⟩ rows32 ⟨(317/400),(-1172077749357/5000000000000),(2172360110218621/20000000000000000)⟩ := by decide +kernel
theorem valid32 : rows32.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain33 : Chain ⟨(317/400),(-1172077749357/5000000000000),(2172360110218621/20000000000000000)⟩ rows33 ⟨(1593/2000),(-2404231862593/10000000000000),(4306734259384791/40000000000000000)⟩ := by decide +kernel
theorem valid33 : rows33.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain34 : Chain ⟨(1593/2000),(-2404231862593/10000000000000),(4306734259384791/40000000000000000)⟩ rows34 ⟨(1601/2000),(-2465178899907/10000000000000),(853556024168957/8000000000000000)⟩ := by decide +kernel
theorem valid34 : rows34.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain35 : Chain ⟨(1601/2000),(-2465178899907/10000000000000),(853556024168957/8000000000000000)⟩ rows35 ⟨(1609/2000),(-505403826889/2000000000000),(4227843759100673/40000000000000000)⟩ := by decide +kernel
theorem valid35 : rows35.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain36 : Chain ⟨(1609/2000),(-505403826889/2000000000000),(4227843759100673/40000000000000000)⟩ rows36 ⟨(1617/2000),(-2589856510741/10000000000000),(4186910302288047/40000000000000000)⟩ := by decide +kernel
theorem valid36 : rows36.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain37 : Chain ⟨(1617/2000),(-2589856510741/10000000000000),(4186910302288047/40000000000000000)⟩ rows37 ⟨(13/16),(-2654170448143/10000000000000),(4144960144553469/40000000000000000)⟩ := by decide +kernel
theorem valid37 : rows37.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain38 : Chain ⟨(13/16),(-2654170448143/10000000000000),(4144960144553469/40000000000000000)⟩ rows38 ⟨(1633/2000),(-2719875383187/10000000000000),(820393873667433/8000000000000000)⟩ := by decide +kernel
theorem valid38 : rows38.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain39 : Chain ⟨(1633/2000),(-2719875383187/10000000000000),(820393873667433/8000000000000000)⟩ rows39 ⟨(1641/2000),(-2786995888641/10000000000000),(4057916855466187/40000000000000000)⟩ := by decide +kernel
theorem valid39 : rows39.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain40 : Chain ⟨(1641/2000),(-2786995888641/10000000000000),(4057916855466187/40000000000000000)⟩ rows40 ⟨(1649/2000),(-2855720063287/10000000000000),(4012776285205333/40000000000000000)⟩ := by decide +kernel
theorem valid40 : rows40.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain41 : Chain ⟨(1649/2000),(-2855720063287/10000000000000),(4012776285205333/40000000000000000)⟩ rows41 ⟨(1657/2000),(-731286690543/2500000000000),(991632559445667/10000000000000000)⟩ := by decide +kernel
theorem valid41 : rows41.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain42 : Chain ⟨(1657/2000),(-731286690543/2500000000000),(991632559445667/10000000000000000)⟩ rows42 ⟨(333/400),(-2995245875071/10000000000000),(3919168007661839/40000000000000000)⟩ := by decide +kernel
theorem valid42 : rows42.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain43 : Chain ⟨(333/400),(-2995245875071/10000000000000),(3919168007661839/40000000000000000)⟩ rows43 ⟨(1673/2000),(-3066033872477/10000000000000),(3870678716111083/40000000000000000)⟩ := by decide +kernel
theorem valid43 : rows43.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain44 : Chain ⟨(1673/2000),(-3066033872477/10000000000000),(3870678716111083/40000000000000000)⟩ rows44 ⟨(1681/2000),(-313752895431/1000000000000),(1910525578765937/20000000000000000)⟩ := by decide +kernel
theorem valid44 : rows44.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain45 : Chain ⟨(1681/2000),(-313752895431/1000000000000),(1910525578765937/20000000000000000)⟩ rows45 ⟨(1689/2000),(-64195092487/200000000000),(1885136912545919/20000000000000000)⟩ := by decide +kernel
theorem valid45 : rows45.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain46 : Chain ⟨(1689/2000),(-64195092487/200000000000),(1885136912545919/20000000000000000)⟩ rows46 ⟨(1697/2000),(-1641373431133/5000000000000),(1859167397188329/20000000000000000)⟩ := by decide +kernel
theorem valid46 : rows46.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain47 : Chain ⟨(1697/2000),(-1641373431133/5000000000000),(1859167397188329/20000000000000000)⟩ rows47 ⟨(341/400),(-3356521539773/10000000000000),(3665221722156037/40000000000000000)⟩ := by decide +kernel
theorem valid47 : rows47.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain48 : Chain ⟨(341/400),(-3356521539773/10000000000000),(3665221722156037/40000000000000000)⟩ rows48 ⟨(1713/2000),(-171550410313/500000000000),(1805461161831877/20000000000000000)⟩ := by decide +kernel
theorem valid48 : rows48.all (fun p => decide p.Valid) = true := by decide +kernel

theorem chain49 : Chain ⟨(1713/2000),(-171550410313/500000000000),(1805461161831877/20000000000000000)⟩ rows49 ⟨(1721/2000),(-175297695727/500000000000),(888856785514133/10000000000000000)⟩ := by decide +kernel
theorem valid49 : rows49.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chain50 : Chain ⟨(1721/2000),(-175297695727/500000000000),(888856785514133/10000000000000000)⟩ rows50 ⟨1,-1,0⟩ := by decide +kernel
theorem valid50 : rows50.all (fun p => decide p.Valid) = true := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 100000000

theorem data_chain : Chain startKnot pieces endKnot := by
  unfold pieces
  simp only [List.append_assoc]
  exact (Chain.append (ps:=rows00) chain00 (Chain.append (ps:=rows01) chain01 (Chain.append (ps:=rows02) chain02 (Chain.append (ps:=rows03) chain03 (Chain.append (ps:=rows04) chain04 (Chain.append (ps:=rows05) chain05 (Chain.append (ps:=rows06) chain06 (Chain.append (ps:=rows07) chain07 (Chain.append (ps:=rows08) chain08 (Chain.append (ps:=rows09) chain09 (Chain.append (ps:=rows10) chain10 (Chain.append (ps:=rows11) chain11 (Chain.append (ps:=rows12) chain12 (Chain.append (ps:=rows13) chain13 (Chain.append (ps:=rows14) chain14 (Chain.append (ps:=rows15) chain15 (Chain.append (ps:=rows16) chain16 (Chain.append (ps:=rows17) chain17 (Chain.append (ps:=rows18) chain18 (Chain.append (ps:=rows19) chain19 (Chain.append (ps:=rows20) chain20 (Chain.append (ps:=rows21) chain21 (Chain.append (ps:=rows22) chain22 (Chain.append (ps:=rows23) chain23 (Chain.append (ps:=rows24) chain24 (Chain.append (ps:=rows25) chain25 (Chain.append (ps:=rows26) chain26 (Chain.append (ps:=rows27) chain27 (Chain.append (ps:=rows28) chain28 (Chain.append (ps:=rows29) chain29 (Chain.append (ps:=rows30) chain30 (Chain.append (ps:=rows31) chain31 (Chain.append (ps:=rows32) chain32 (Chain.append (ps:=rows33) chain33 (Chain.append (ps:=rows34) chain34 (Chain.append (ps:=rows35) chain35 (Chain.append (ps:=rows36) chain36 (Chain.append (ps:=rows37) chain37 (Chain.append (ps:=rows38) chain38 (Chain.append (ps:=rows39) chain39 (Chain.append (ps:=rows40) chain40 (Chain.append (ps:=rows41) chain41 (Chain.append (ps:=rows42) chain42 (Chain.append (ps:=rows43) chain43 (Chain.append (ps:=rows44) chain44 (Chain.append (ps:=rows45) chain45 (Chain.append (ps:=rows46) chain46 (Chain.append (ps:=rows47) chain47 (Chain.append (ps:=rows48) chain48 (Chain.append (ps:=rows49) chain49 (Chain.append (ps:=rows50) chain50 (show Chain endKnot [] endKnot from rfl))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem data_valid : ∀ p ∈ pieces, p.Valid := by
  have combine {x y : List Piece} (hx : ∀ p∈x,p.Valid) (hy : ∀ p∈y,p.Valid) : ∀ p∈x++y,p.Valid := by
    intro p hp; rcases List.mem_append.mp hp with h|h; exact hx p h; exact hy p h
  unfold pieces
  simp only [List.append_assoc]
  have v00 : ∀ p∈rows00,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid00 p hp)
  have v01 : ∀ p∈rows01,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid01 p hp)
  have v02 : ∀ p∈rows02,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid02 p hp)
  have v03 : ∀ p∈rows03,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid03 p hp)
  have v04 : ∀ p∈rows04,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid04 p hp)
  have v05 : ∀ p∈rows05,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid05 p hp)
  have v06 : ∀ p∈rows06,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid06 p hp)
  have v07 : ∀ p∈rows07,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid07 p hp)
  have v08 : ∀ p∈rows08,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid08 p hp)
  have v09 : ∀ p∈rows09,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid09 p hp)
  have v10 : ∀ p∈rows10,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid10 p hp)
  have v11 : ∀ p∈rows11,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid11 p hp)
  have v12 : ∀ p∈rows12,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid12 p hp)
  have v13 : ∀ p∈rows13,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid13 p hp)
  have v14 : ∀ p∈rows14,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid14 p hp)
  have v15 : ∀ p∈rows15,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid15 p hp)
  have v16 : ∀ p∈rows16,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid16 p hp)
  have v17 : ∀ p∈rows17,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid17 p hp)
  have v18 : ∀ p∈rows18,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid18 p hp)
  have v19 : ∀ p∈rows19,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid19 p hp)
  have v20 : ∀ p∈rows20,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid20 p hp)
  have v21 : ∀ p∈rows21,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid21 p hp)
  have v22 : ∀ p∈rows22,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid22 p hp)
  have v23 : ∀ p∈rows23,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid23 p hp)
  have v24 : ∀ p∈rows24,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid24 p hp)
  have v25 : ∀ p∈rows25,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid25 p hp)
  have v26 : ∀ p∈rows26,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid26 p hp)
  have v27 : ∀ p∈rows27,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid27 p hp)
  have v28 : ∀ p∈rows28,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid28 p hp)
  have v29 : ∀ p∈rows29,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid29 p hp)
  have v30 : ∀ p∈rows30,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid30 p hp)
  have v31 : ∀ p∈rows31,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid31 p hp)
  have v32 : ∀ p∈rows32,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid32 p hp)
  have v33 : ∀ p∈rows33,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid33 p hp)
  have v34 : ∀ p∈rows34,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid34 p hp)
  have v35 : ∀ p∈rows35,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid35 p hp)
  have v36 : ∀ p∈rows36,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid36 p hp)
  have v37 : ∀ p∈rows37,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid37 p hp)
  have v38 : ∀ p∈rows38,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid38 p hp)
  have v39 : ∀ p∈rows39,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid39 p hp)
  have v40 : ∀ p∈rows40,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid40 p hp)
  have v41 : ∀ p∈rows41,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid41 p hp)
  have v42 : ∀ p∈rows42,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid42 p hp)
  have v43 : ∀ p∈rows43,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid43 p hp)
  have v44 : ∀ p∈rows44,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid44 p hp)
  have v45 : ∀ p∈rows45,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid45 p hp)
  have v46 : ∀ p∈rows46,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid46 p hp)
  have v47 : ∀ p∈rows47,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid47 p hp)
  have v48 : ∀ p∈rows48,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid48 p hp)
  have v49 : ∀ p∈rows49,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid49 p hp)
  have v50 : ∀ p∈rows50,p.Valid := fun p hp => of_decide_eq_true (List.all_eq_true.mp valid50 p hp)
  exact (combine (x:=rows00) v00 (combine (x:=rows01) v01 (combine (x:=rows02) v02 (combine (x:=rows03) v03 (combine (x:=rows04) v04 (combine (x:=rows05) v05 (combine (x:=rows06) v06 (combine (x:=rows07) v07 (combine (x:=rows08) v08 (combine (x:=rows09) v09 (combine (x:=rows10) v10 (combine (x:=rows11) v11 (combine (x:=rows12) v12 (combine (x:=rows13) v13 (combine (x:=rows14) v14 (combine (x:=rows15) v15 (combine (x:=rows16) v16 (combine (x:=rows17) v17 (combine (x:=rows18) v18 (combine (x:=rows19) v19 (combine (x:=rows20) v20 (combine (x:=rows21) v21 (combine (x:=rows22) v22 (combine (x:=rows23) v23 (combine (x:=rows24) v24 (combine (x:=rows25) v25 (combine (x:=rows26) v26 (combine (x:=rows27) v27 (combine (x:=rows28) v28 (combine (x:=rows29) v29 (combine (x:=rows30) v30 (combine (x:=rows31) v31 (combine (x:=rows32) v32 (combine (x:=rows33) v33 (combine (x:=rows34) v34 (combine (x:=rows35) v35 (combine (x:=rows36) v36 (combine (x:=rows37) v37 (combine (x:=rows38) v38 (combine (x:=rows39) v39 (combine (x:=rows40) v40 (combine (x:=rows41) v41 (combine (x:=rows42) v42 (combine (x:=rows43) v43 (combine (x:=rows44) v44 (combine (x:=rows45) v45 (combine (x:=rows46) v46 (combine (x:=rows47) v47 (combine (x:=rows48) v48 (combine (x:=rows49) v49 (combine (x:=rows50) v50 (by simp))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem data_nonempty : pieces ≠ [] := by decide +kernel
theorem central_mem : centralPiece ∈ pieces := by decide +kernel
theorem central_data : centralPiece.lo=rcQ ∧ centralPiece.hi=zdepQ ∧ centralPiece.coeff=[lamQ-rcQ,-1] := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
noncomputable section

theorem Chain.exists_piece {ps : List Piece} {a b : Knot} (h : Chain a ps b)
    {x : ℝ} (hx : (a.x:ℝ)≤x) (hx' : x≤(b.x:ℝ)) (hne : ps ≠ []) :
    ∃ p ∈ ps, x ∈ Icc (p.lo:ℝ) p.hi := by
  induction ps generalizing a with
  | nil => contradiction
  | cons p ps ih =>
    rcases h with ⟨rfl,_,hh⟩
    by_cases hp : x≤(p.hi:ℝ)
    · exact ⟨p,List.mem_cons_self, hx,hp⟩
    · have hne' : ps≠[] := by
        rintro rfl
        have he : p.last=b := hh
        exact hp (by simpa [← he,Piece.last] using hx')
      obtain ⟨q,hq,hxq⟩ := ih hh (le_of_not_ge hp) hne'
      exact ⟨q,List.mem_cons_of_mem _ hq,hxq⟩

theorem Chain.continuous_score {ps : List Piece} {a b : Knot} (h : Chain a ps b) :
    ContinuousOn (scoreEval b ps) (Icc (a.x:ℝ) b.x) := by
  induction ps generalizing a with
  | nil => exact continuousOn_const
  | cons p ps ih =>
    rcases h with ⟨rfl,hp,ch⟩
    have ab : (p.lo:ℝ)≤p.hi := by exact_mod_cast hp.le
    have bc : (p.hi:ℝ)≤b.x := by exact_mod_cast ch.le
    change ContinuousOn _ (Icc (p.lo:ℝ) b.x)
    rw [← Icc_union_Icc_eq_Icc ab bc]
    apply ContinuousOn.union_of_isClosed _ _ isClosed_Icc isClosed_Icc
    · exact p.continuous_value.continuousOn.congr (fun x hx => if_pos hx.2)
    · exact (ih ch).congr (fun x hx => select_right p ch _ Knot.y start_value end_value hx.1)

theorem Chain.antitone_scoreOn {ps : List Piece} {a b : Knot} (h : Chain a ps b)
    (l : ℝ) (k : ℝ) (hm : ∀ p ∈ ps,
      AntitoneOn (fun x => p.value x+k*x) (Icc (max l (p.lo:ℝ)) p.hi)) :
    AntitoneOn (fun x => scoreEval b ps x+k*x) (Icc (max l (a.x:ℝ)) b.x) := by
  induction ps generalizing a with
  | nil =>
    have he : a=b := h
    intro x hx y hy hxy
    have hxx := (le_max_right l (a.x:ℝ)).trans hx.1
    have hyy := (le_max_right l (a.x:ℝ)).trans hy.1
    rw [←he] at hx hy
    have h : x=y := by linarith [hx.2,hy.2]
    rw [h]
  | cons p ps ih =>
    rcases h with ⟨rfl,hp,ch⟩
    have f := hm p List.mem_cons_self
    have g := ih ch (fun q hq => hm q (List.mem_cons_of_mem _ hq))
    intro x hx y hy hxy
    change max l (p.lo:ℝ)≤x ∧ x≤b.x at hx
    change max l (p.lo:ℝ)≤y ∧ y≤b.x at hy
    by_cases hyy : y≤(p.hi:ℝ)
    · have hh := f ⟨hx.1,hxy.trans hyy⟩ ⟨hy.1,hyy⟩ hxy
      simpa only [scoreEval,select,if_pos hyy,if_pos (hxy.trans hyy)] using hh
    have ry := select_right p ch _ Knot.y start_value end_value (le_of_not_ge hyy)
    by_cases hxx : (p.hi:ℝ)≤x
    · have rx := select_right p ch _ Knot.y start_value end_value hxx
      change select _ _ _ y+k*y ≤ select _ _ _ x+k*x
      rw [rx,ry]
      exact g ⟨max_le (le_max_left _ _ |>.trans hx.1) hxx,hx.2⟩
        ⟨max_le (le_max_left _ _ |>.trans hy.1) (le_of_not_ge hyy),hy.2⟩ hxy
    · have hxh := le_of_not_ge hxx
      have hl := (le_max_left _ _ |>.trans hx.1).trans hxh
      have hp' : (p.lo:ℝ)≤p.hi := by exact_mod_cast hp.le
      have hyh : (p.hi:ℝ)≤y := le_of_not_ge hyy
      have hmid := g ⟨max_le hl le_rfl, (by exact_mod_cast ch.le : (p.hi:ℝ) ≤ b.x)⟩
        ⟨max_le (le_max_left _ _ |>.trans hy.1) hyh,hy.2⟩ hyh
      have hleft := f ⟨hx.1,hxh⟩ ⟨max_le hl hp',le_rfl⟩ hxh
      change select _ _ _ y+k*y ≤ select _ _ _ x+k*x
      rw [ry,select,if_pos hxh]
      refine hmid.trans ?_
      have e : scoreEval b ps (p.hi:ℝ)=p.value p.hi :=
        (select_start ch _ Knot.y start_value).trans (end_value p).symm
      change scoreEval b ps (p.hi:ℝ) + k*(p.hi:ℝ) ≤ p.value x + k*x
      rw [e]
      exact hleft

theorem Chain.integral_score {ps : List Piece} {a b : Knot} (h : Chain a ps b) {x : ℝ}
    (hx : x∈Icc (a.x:ℝ) b.x) :
    ∫ y in (a.x:ℝ)..x, scoreEval b ps y = primitiveEval b ps x-(a.j:ℝ) := by
  induction ps generalizing a with
  | nil =>
    have he : a=b := h
    subst b
    have : x=a.x := le_antisymm hx.2 hx.1
    simp [this,primitiveEval,select]
  | cons p ps ih =>
    rcases h with ⟨rfl,hp,ch⟩
    change ∫ y in (p.lo:ℝ)..x, scoreEval b (p::ps) y = primitiveEval b (p::ps) x - _
    have pref {z : ℝ} (h0 : (p.lo:ℝ)≤z) (h1 : z≤(p.hi:ℝ)) :
        ∫ y in (p.lo:ℝ)..z, scoreEval b (p::ps) y = p.primitiveValue z-(p.first.j:ℝ) := by
      calc
        _ = ∫ y in (p.lo:ℝ)..z, p.value y := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le h0] at hy
          exact if_pos (hy.2.trans h1)
        _ = _ := by
          rw [←start_primitive]
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => p.hasDeriv_primitive y)
            (p.continuous_value.intervalIntegrable _ _)
    by_cases hx1 : x≤(p.hi:ℝ)
    · simpa only [primitiveEval,select,if_pos hx1] using pref hx.1 hx1
    have ph : (p.lo:ℝ)≤p.hi := by exact_mod_cast hp.le
    have xp : (p.hi:ℝ)≤x := le_of_not_ge hx1
    have intreg := (show Chain p.first (p::ps) b from ⟨rfl,hp,ch⟩).continuous_score
    have ia := (intreg.mono (Icc_subset_Icc_right (xp.trans hx.2))).intervalIntegrable_of_Icc (μ:=volume) ph
    have ib := (intreg.mono (Icc_subset_Icc ph hx.2)).intervalIntegrable_of_Icc (μ:=volume) xp
    have jr : ∫ y in (p.hi:ℝ)..x, scoreEval b (p::ps) y =
        primitiveEval b ps x-(p.last.j:ℝ) := by
      rw [← ih ch ⟨xp,hx.2⟩]
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le xp] at hy
      exact select_right p ch _ Knot.y start_value end_value hy.1
    rw [←intervalIntegral.integral_add_adjacent_intervals ia ib,pref ph le_rfl,jr,end_primitive]
    change _ = select _ _ _ x - _
    rw [select_right p ch _ Knot.j start_primitive end_primitive xp]
    unfold primitiveEval
    ring

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set
noncomputable section

theorem score_on_piece {p : Piece} (hp : p∈pieces) {x : ℝ} (hx : x∈Icc (p.lo:ℝ) p.hi) :
    score x=p.value x :=
  select_mem data_chain _ Knot.y start_value end_value hp hx

theorem score_continuous : ContinuousOn score (Icc 0 1) := by
  simpa [score,startKnot,endKnot] using data_chain.continuous_score

theorem score_antitone : AntitoneOn score (Icc 0 1) := by
  have hm := data_chain.antitone_scoreOn 0 0 (by
    intro p hp
    have hh := p.antitone_score (data_valid p hp)
    simpa using hh.mono (Icc_subset_Icc_left (le_max_right _ _)))
  simpa [score,startKnot,endKnot] using hm

theorem score_central {x : ℝ} (hx : x∈Icc rc zdep) : score x=lam-x := by
  obtain ⟨hl,hr,hc⟩ := central_data
  have hx' : x∈Icc (centralPiece.lo:ℝ) centralPiece.hi := by simpa [hl,hr,rc,zdep] using hx
  rw [score_on_piece central_mem hx',centralPiece.linear_value (by rwa [hl])]

theorem J_score {x : ℝ} (hx : x∈Icc 0 1) : J score x=primitive x := by
  have h := data_chain.integral_score (x:=x) (by simpa [startKnot,endKnot] using hx)
  simpa [J,score,primitive,startKnot,endKnot] using h

theorem score_add_antitone : AntitoneOn (fun x => score x + x) (Icc lam 1) := by
  have hm := data_chain.antitone_scoreOn lam 1 (by
    intro p hp
    rcases (data_valid p hp).2.2 with ⟨hr,_,_⟩|⟨_,_,hc⟩|⟨_,hd,_⟩
    · intro x hx y hy _
      have hrl : rc < lam := by norm_num [rc,rcQ,lam,lamQ]
      have HH : (p.hi:ℝ) ≤ rc := by unfold rc; exact_mod_cast hr
      exact False.elim (hrl.not_ge ((le_max_left _ _).trans (hx.1.trans (hx.2.trans HH))))
    · simp only [one_mul,p.linear_value hc,sub_add_cancel]
      exact antitoneOn_const
    · simpa using (p.antitone_score_add hd).mono (Icc_subset_Icc_left (le_max_right _ _)))
  simpa [score,startKnot,endKnot,show (0:ℝ) ≤ lam by norm_num [lam,lamQ],max_eq_left] using hm

theorem score_isScoreFunction : IsScoreFunction lam score := by
  refine ⟨by norm_num [lam,lamQ],score_continuous,score_antitone,?_,?_,?_,?_⟩
  · change J score 1 = 0
    rw [J_score (by norm_num)]
    have h := data_chain.select_end_primitive
    simpa [primitive,endKnot] using h
  · simpa [score,endKnot] using data_chain.select_end_score
  · intro x hx
    have hbounds : (0:ℝ) ≤ rc ∧ rc < lam ∧ lam < zdep ∧ zdep ≤ 1 := by
      norm_num [lam,lamQ,rc,rcQ,zdep,zdepQ]
    by_cases hrc : rc ≤ x
    · rw [score_central ⟨hrc,hx.2.le.trans hbounds.2.2.1.le⟩]; linarith [hx.2]
    · have hh := score_antitone ⟨hx.1,hx.2.le.trans (hbounds.2.2.1.le.trans hbounds.2.2.2)⟩
          ⟨hbounds.1,hbounds.2.1.le.trans (hbounds.2.2.1.le.trans hbounds.2.2.2)⟩ (le_of_not_ge hrc)
      rw [score_central ⟨le_rfl,hbounds.2.1.le.trans hbounds.2.2.1.le⟩] at hh
      linarith [hbounds.2.1]
  · intro x hx
    obtain ⟨p,hp,hx'⟩ := data_chain.exists_piece (x:=x) (by simpa [startKnot] using hx.1)
      (by simpa [endKnot] using hx.2) data_nonempty
    rw [score_on_piece hp hx']
    exact p.ceiling (data_valid p hp) hx'

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox


namespace Bounds
def Holds (i : Bounds) (x : ℝ) : Prop := (i.lo:ℝ) ≤ x ∧ x ≤ (i.hi:ℝ)

def hull (i j : Bounds) : Bounds := ⟨min i.lo j.lo,max i.hi j.hi⟩
def meet (i j : Bounds) : Bounds := ⟨max i.lo j.lo,min i.hi j.hi⟩
def reciprocal (i : Bounds) : Bounds := ⟨i.hi⁻¹,i.lo⁻¹⟩
def horner (coeff : List ℚ) (i : Bounds) : Bounds :=
  coeff.foldr (fun a acc => (point a).plus (i.times acc)) (point 0)

end Bounds
end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds Set


end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem primitive_sandwich {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b-a)*ϕ b ≤ J ϕ b - J ϕ a ∧ J ϕ b - J ϕ a ≤ (b-a)*ϕ a := by
  have hi {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : IntervalIntegrable ϕ volume x y :=
    (h.continuousOn.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have hdiff : J ϕ b - J ϕ a = ∫ r in a..b, ϕ r := by
    have hs := intervalIntegral.integral_add_adjacent_intervals (hi (le_refl 0) ha (hab.trans hb)) (hi ha hab hb)
    unfold J
    linarith
  rw [hdiff]
  have hlow := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := ϕ b)) (hi ha hab hb)
    (fun r hr => h.antitoneOn ⟨ha.trans hr.1, hr.2.trans hb⟩ ⟨ha.trans hab, hb⟩ hr.2)
  have hhi := intervalIntegral.integral_mono_on hab (hi ha hab hb) (intervalIntegrable_const (c := ϕ a))
    (fun r hr => h.antitoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hr.1, hr.2.trans hb⟩ hr.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using And.intro hlow hhi

theorem eq_43_44 {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ) :
    (∀ p q, 0 ≤ q → q ≤ p → p ≤ 1 →
      deltaP ϕ p q ≤ p - q ∧ deltaP ϕ p q ≤ (1 - p) * ϕ q ∧ q * ϕ q ≤ J ϕ q) ∧
      ∀ p q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 → KP ϕ p q z ≤ -(p - q) * ϕ z - J ϕ q := by
  have h0 : J ϕ 0 = 0 := by simp [J]
  have h1 : J ϕ 1 = 0 := hϕ.integral_eq_zero
  have hleft (r : ℝ) (hr : r ∈ Icc 0 1) := (primitive_sandwich hϕ (le_refl 0) hr.1 hr.2).1
  have hright (r : ℝ) (hr : r ∈ Icc 0 1) := primitive_sandwich hϕ hr.1 hr.2 (le_refl 1)
  simp only [h0,h1,hϕ.at_one,sub_zero,zero_sub] at hleft hright
  have hJ (r : ℝ) (hr : r ∈ Icc 0 1) : 0 ≤ J ϕ r := by
    by_cases hp : 0 ≤ ϕ r
    · exact (mul_nonneg hr.1 hp).trans (hleft r hr)
    · have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2) (le_of_not_ge hp)
      linarith [(hright r hr).2]
  constructor
  · intro p q hq hqp hp
    let r := 1-p+q
    have hr : r ∈ Icc 0 1 := ⟨by dsimp [r]; linarith,by dsimp [r]; linarith⟩
    have hs := primitive_sandwich hϕ hq (show q≤r by dsimp [r]; linarith) hr.2
    have he : r-q=1-p := by dsimp [r]; ring
    rw [he] at hs
    change J ϕ r - J ϕ q ≤ _ ∧ J ϕ r - J ϕ q ≤ _ ∧ _
    refine ⟨?_,hs.2,hleft q ⟨hq,hqp.trans hp⟩⟩
    have hh := (hright r hr).1
    dsimp [r] at hh ⊢
    linarith [hJ q ⟨hq,hqp.trans hp⟩]
  · intro p q z hq hqp hpz hz
    have h := (primitive_sandwich hϕ (show 0≤z-p+q by linarith) (show z-p+q≤z by linarith) hz).1
    have he : z-(z-p+q)=p-q := by ring
    rw [he] at h
    unfold KP
    linarith

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperBox.Bounds
noncomputable section

def qselect (v : Piece → ℚ → ℚ) (ending : ℚ) : List Piece → ℚ → ℚ
  | [], _ => ending
  | p::ps,x => if x≤p.hi then v p x else qselect v ending ps x

theorem cast_qselect (qv : Piece → ℚ → ℚ) (v : Piece → ℝ → ℝ)
    (h : ∀ p x, (qv p x:ℝ)=v p (x:ℝ)) (ending : ℚ) (ps : List Piece) (x : ℚ) :
    (qselect qv ending ps x : ℝ) = select v ending ps (x:ℝ) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hx : x≤p.hi
    · simpa only [qselect,select,if_pos hx,if_pos (by exact_mod_cast hx : (x:ℝ)≤p.hi)] using h p x
    · simpa only [qselect,select,if_neg hx,if_neg (by exact_mod_cast hx : ¬(x:ℝ)≤p.hi)] using ih

def qscore (x : ℚ) : ℚ := qselect Piece.qvalue endKnot.y pieces x
def qprimitive (x : ℚ) : ℚ := qselect Piece.qprimitive endKnot.j pieces x

theorem qprimitive_exact (x : ℚ) : (qprimitive x:ℝ)=primitive x :=
  cast_qselect _ _ Piece.cast_qprimitive _ _ x

private theorem bounds_lam : (0:ℝ)<lam ∧ lam<1 := score_isScoreFunction.lam_mem

theorem primitive_decreases : AntitoneOn (J score) (Icc lam 1) := by
  intro x hx y hy hxy
  have hh := (primitive_sandwich score_isScoreFunction (bounds_lam.1.le.trans hx.1) hxy hy.2).2
  have hc := score_isScoreFunction.le_lam_sub x ⟨bounds_lam.1.le.trans hx.1,hx.2⟩
  have hs : score x≤0 := by linarith [hx.1]
  linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hs]

def scoreBox (i : Bounds) : Bounds :=
  decreasingRange (fun q => Bounds.point (qscore q)) (i.meet ⟨0,1⟩)
def primitiveBox (i : Bounds) : Bounds :=
  unimodalRange (fun q => Bounds.point (qprimitive q)) lamQ (i.meet ⟨0,1⟩)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true

namespace StableVotingDistortion.PaperMiddle

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem knot_order : (knots.map Knot.position).IsChain (· < ·) := by decide +kernel
theorem knot_endpoints : (knots.head!).position=60 ∧ (knots.getLast!).position=640 := by decide +kernel
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true

namespace StableVotingDistortion.PaperMiddle
open Set
noncomputable section

def rc : ℝ := 4356751/12500000
def p0 : ℝ := 1/100

theorem interpolate_eq (col : Knot → ℕ) (k l : Knot) (x : ℝ)
    (hkl : rank k<rank l) (hx : x∈Icc (rank k) (rank l)) :
    interpolate col k l x=value col k+
      ((value col l-value col k)/(rank l-rank k))*(x-rank k) := by
  have hpos := sub_pos.mpr hkl
  have ht : 0≤(x-rank k)/(rank l-rank k) := div_nonneg (sub_nonneg.mpr hx.1) hpos.le
  have ho : (x-rank k)/(rank l-rank k)≤1 := (div_le_one hpos).mpr (by linarith [hx.2])
  simp only [interpolate,fraction,min_eq_right ho,max_eq_right ht]
  ring

private theorem lookup_nonneg (col : Knot → ℕ) (x : ℝ) (k : Knot) (ks : List Knot) :
    0≤lookup col x k ks := by
  induction ks generalizing k with
  | nil => dsimp [lookup,value];positivity
  | cons l tail ih =>
    rw [lookup];split_ifs
    · have h0 : 0≤fraction x (rank k) (rank l) := le_max_left _ _
      have h1 : fraction x (rank k) (rank l)≤1 := max_le zero_le_one (min_le_left _ _)
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr h1) (by unfold value;positivity))
        (mul_nonneg h0 (by unfold value;positivity))
    · exact ih l

theorem entry_nonneg (col : Knot → ℕ) (p : ℝ) : 0≤entry col p := lookup_nonneg _ _ _ _


private theorem find_cell (p : ℝ) (k l : Knot) (tail : List Knot)
    (h : (k::l::tail).IsChain (fun x y => x.position<y.position))
    (hlo : rank k≤p) (hhi : p≤rank ((k::l::tail).getLast!)) :
    ∃ c d : Knot, (c,d)∈(k::l::tail).zip (l::tail) ∧
      rank c<rank d ∧ p∈Icc (rank c) (rank d) ∧
      ∀ col : Knot → ℕ,lookup col p k (l::tail)=interpolate col c d p := by
  by_cases hpl : p≤rank l
  · refine ⟨k,l,by simp,?_,⟨hlo,hpl⟩,fun col => by simp [lookup,hpl]⟩
    have hlt := h.rel
    exact div_lt_div_of_pos_right (by exact_mod_cast hlt) (by norm_num)
  · cases tail with
    | nil => simp at hhi;exact (hpl hhi).elim
    | cons m rest =>
      obtain ⟨c,d,hm,hcd,hmem,he⟩ := find_cell p l m rest h.tail (le_of_not_ge hpl) (by simpa using hhi)
      exact ⟨c,d,by simpa only [List.zip_cons_cons,List.mem_cons] using Or.inr hm,hcd,hmem,
        fun col => by simpa only [lookup,if_neg hpl] using he col⟩
termination_by tail.length

theorem lp_cell {p : ℝ} (hp : p∈Icc pA pC) :
    ∃ c d : Knot,(c,d)∈adjacentCells ∧ rank c<rank d ∧ p∈Icc (rank c) (rank d) ∧
      ∀ col : Knot → ℕ,entry col p=interpolate col c d p := by
  have hchain : knots.IsChain (fun x y => x.position<y.position) := (List.isChain_map Knot.position).mp knot_order
  have sn : knots.head!::knots.tail.head!::knots.tail.tail=knots := by rfl
  have hlast : rank knots.getLast! = pC := by change (knots.getLast!.position:ℝ)/1000=_; rw [knot_endpoints.2];norm_num [pC]
  have hfirst : rank knots.head! = pA := by change (knots.head!.position:ℝ)/1000=_;rw [knot_endpoints.1];norm_num [pA]
  have hl : p≤rank ((knots.head!::knots.tail.head!::knots.tail.tail).getLast!) := by rw [sn,hlast];exact hp.2
  have h := find_cell p knots.head! knots.tail.head! knots.tail.tail (by rw [sn];exact hchain) (by rw [hfirst];exact hp.1) hl
  exact h


structure RegimeBounds (φ : ℝ → ℝ) : Prop where
  constant : ∀ p ∈ Icc p0 pA,PaperBox.CubeBounds lam rc φ beta0 (-1) (1+beta0*p) p
  lpBelow : ∀ p ∈ Icc pA lam,PaperBox.CubeBounds lam rc φ (entry Knot.beta p) (-1) (entry Knot.eta p) p
  lpAbove : ∀ p ∈ Icc lam pC,PaperBox.CubeBounds lam rc φ (entry Knot.beta p) (-1) (entry Knot.eta p) p
  canon : ∀ p ∈ Icc pC p1,PaperBox.CubeBounds lam rc φ (canonical φ p) 1 (-(canonical φ p*(1-p))) p

theorem beta_nonneg {φ : ℝ → ℝ} (hs : IsScoreFunction lam φ) {p : ℝ} (hp : p∈Ioo 0 1) : 0≤beta φ p := by
  have hJ : 0≤J φ p := by
    by_cases hφ : 0≤φ p
    · have h := (primitive_sandwich hs (le_refl 0) hp.1.le hp.2.le).1
      simp only [J,intervalIntegral.integral_same,sub_zero] at h
      exact (mul_nonneg hp.1.le hφ).trans h
    · have h := (primitive_sandwich hs hp.1.le hp.2.le (le_refl 1)).2
      rw [show J φ 1=0 from hs.integral_eq_zero,zero_sub] at h
      linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp.2.le) (le_of_not_ge hφ)]
  unfold beta
  split_ifs
  · norm_num [beta0]
  · exact entry_nonneg _ _
  · exact mul_nonneg (div_nonneg hp.1.le hJ) (by norm_num [eps])
  · exact div_nonneg hp.1.le hJ

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds

inductive Expr (d : ℕ) where
  | const (k : ℚ)
  | coord (j : Fin d)
  | add (a b : Expr d)
  | neg (a : Expr d)
  | mul (a b : Expr d)
  | inv (a : Expr d)
  | pos (a : Expr d)
  | atom (f : Fin 4) (a : Expr d)
  | potential (r y : Expr d)
deriving Repr

def Inside {d : ℕ} (b : Box d) (x : Fin d → ℝ) : Prop := ∀ j, (b j).Holds (x j)

noncomputable def Expr.value {d : ℕ} (fs : Fin 4 → ℝ → ℝ) (pot : ℝ → ℝ → ℝ)
    (x : Fin d → ℝ) : Expr d → ℝ
  | .const k => k
  | .coord j => x j
  | .add a b => a.value fs pot x + b.value fs pot x
  | .neg a => -a.value fs pot x
  | .mul a b => a.value fs pot x * b.value fs pot x
  | .inv a => (a.value fs pot x)⁻¹
  | .pos a => max (a.value fs pot x) 0
  | .atom f a => fs f (a.value fs pot x)
  | .potential r y => pot (r.value fs pot x) (y.value fs pot x)

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open PaperBox
open Set
noncomputable section


inductive Family | L1 | L2 | L3 | L3id | L4 | L4id deriving DecidableEq,Repr
inductive Regime | constant | lp | canonical deriving DecidableEq,Repr
inductive Side | below | above deriving DecidableEq,Repr

abbrev Family.dim : Family → ℕ
  | .L3id => 2
  | .L4 => 4
  | _ => 3

def atoms (φ : ℝ → ℝ) : Fin 4 → ℝ → ℝ := ![φ,J φ,PaperMiddle.entry PaperMiddle.Knot.beta,PaperMiddle.entry PaperMiddle.Knot.eta]

private instance {d : ℕ} : Add (Expr d) := ⟨Expr.add⟩
private instance {d : ℕ} : Neg (Expr d) := ⟨Expr.neg⟩
private instance {d : ℕ} : Sub (Expr d) := ⟨fun x y => x + -y⟩
private instance {d : ℕ} : Mul (Expr d) := ⟨Expr.mul⟩
private instance {d : ℕ} : Div (Expr d) := ⟨fun x y => x*Expr.inv y⟩
private instance {d n : ℕ} : OfNat (Expr d) n := ⟨Expr.const n⟩

private def familyExprLam {d : ℕ} : Expr d := Expr.const (703/1250)
private def familyExprRc {d : ℕ} : Expr d := Expr.const (4356751/12500000)
private def phi {d : ℕ} (x : Expr d) := Expr.atom 0 x
private def prim {d : ℕ} (x : Expr d) := Expr.atom 1 x
private def betaLP {d : ℕ} (x : Expr d) := Expr.atom 2 x
private def etaLP {d : ℕ} (x : Expr d) := Expr.atom 3 x

structure Coeff (T : Type) where
  beta : T
  a : T
  b : T

def coefficients {d : ℕ} (mode : Regime) (p : Expr d) : Coeff (Expr d) :=
  match mode with
  | .constant => ⟨6,-1,1+6*p⟩
  | .lp => ⟨betaLP p,-1,etaLP p⟩
  | .canonical =>
    let B := (p/prim p)*Expr.const (1+1/20000)
    ⟨B,1,-(B*(1-p))⟩

def realCoeff (mode : Regime) (φ : ℝ → ℝ) (p : ℝ) : Coeff ℝ :=
  match mode with
  | .constant => ⟨6,-1,1+6*p⟩
  | .lp => ⟨PaperMiddle.entry PaperMiddle.Knot.beta p,-1,PaperMiddle.entry PaperMiddle.Knot.eta p⟩
  | .canonical =>
    let B := PaperMiddle.canonical φ p
    ⟨B,1,-(B*(1-p))⟩

def first {d : ℕ} (p q x : Expr d) (c : Coeff (Expr d)) :=
  q+c.beta*(prim (1-p+q)-prim q)+(c.a*(familyExprLam-x)+c.b*phi x).pos-familyExprLam

def second {d : ℕ} (p q x : Expr d) (c : Coeff (Expr d)) :=
  q+c.beta*(prim (x-p+q)-prim x-prim q)+(c.a*(familyExprLam-x)+c.b*phi x).pos

def third {d : ℕ} (p q r : Expr d) (c : Coeff (Expr d)) :=
  q+c.beta*(prim (1-p+q)-prim q)+Expr.potential r q-familyExprLam-
    (-phi q).pos*(c.a*r+c.b).pos

def fourth {d : ℕ} (p q z r : Expr d) (c : Coeff (Expr d)) :=
  q+c.beta*(prim (z-p+q)-prim z-prim q)+Expr.potential r q-Expr.potential r z-
    (-phi z).pos*(c.a*r+c.b).pos

private def getRatio {d : ℕ} (w : Expr d) : Expr d :=
  let x := w*familyExprRc
  (familyExprLam-x)/phi x


def expression (mode : Regime) (side : Side) : (kind : Family) → Expr kind.dim
  | .L1 =>
    let p := Expr.coord 0
    let u := Expr.coord 1
    let w := Expr.coord 2
    let q := u*(match side with | .below => p | .above => familyExprLam)
    first p q (q+w*(familyExprLam-q)) (coefficients mode p)
  | .L2 =>
    let p := Expr.coord 0
    second p (Expr.coord 1*p) (p+Expr.coord 2*(familyExprLam-p)) (coefficients mode p)
  | .L3 =>
    let p := Expr.coord 0
    third p (Expr.coord 1*p) (getRatio (Expr.coord 2)) (coefficients mode p)
  | .L3id =>
    let p := Expr.coord 0
    third p (Expr.coord 1*p) 1 (coefficients mode p)
  | .L4 =>
    let p := Expr.coord 0
    fourth p (Expr.coord 1*p) (p+Expr.coord 2*(1-p)) (getRatio (Expr.coord 3)) (coefficients mode p)
  | .L4id =>
    let p := Expr.coord 0
    fourth p (Expr.coord 1*p) (p+Expr.coord 2*(1-p)) 1 (coefficients mode p)

private def target (mode : Regime) (side : Side) (φ : ℝ → ℝ) :
    (kind : Family) → (Fin kind.dim → ℝ) → ℝ
  | .L1,t =>
    let p := t 0
    let c := realCoeff mode φ p
    let q := t 1*(match side with | .below => p | .above => PaperMiddle.lam)
    lowFirst PaperMiddle.lam φ c.beta c.a c.b p q (q+t 2*(PaperMiddle.lam-q))
  | .L2,t =>
    let p := t 0
    let c := realCoeff mode φ p
    lowSecond PaperMiddle.lam φ c.beta c.a c.b p (t 1*p) (p+t 2*(PaperMiddle.lam-p))
  | .L3,t =>
    let p := t 0
    let c := realCoeff mode φ p
    highFirst PaperMiddle.lam φ c.beta c.a c.b p (t 1*p) (ratio PaperMiddle.lam φ (t 2*PaperMiddle.rc))
  | .L3id,t =>
    let p := t 0
    let c := realCoeff mode φ p
    highFirst PaperMiddle.lam φ c.beta c.a c.b p (t 1*p) 1
  | .L4,t =>
    let p := t 0
    let c := realCoeff mode φ p
    highSecond PaperMiddle.lam φ c.beta c.a c.b p (t 1*p) (p+t 2*(1-p)) (ratio PaperMiddle.lam φ (t 3*PaperMiddle.rc))
  | .L4id,t =>
    let p := t 0
    let c := realCoeff mode φ p
    highSecond PaperMiddle.lam φ c.beta c.a c.b p (t 1*p) (p+t 2*(1-p)) 1

def eval (φ : ℝ → ℝ) {d : ℕ} (t : Fin d → ℝ) (e : Expr d) :=
  e.value (atoms φ) (potential PaperMiddle.lam φ) t

private theorem value_sub {d : ℕ} (F : Fin 4 → ℝ → ℝ) (W : ℝ → ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    Expr.value F W t (x-y)=Expr.value F W t x-Expr.value F W t y := by rfl
private theorem value_div {d : ℕ} (F : Fin 4 → ℝ → ℝ) (W : ℝ → ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    Expr.value F W t (x/y)=Expr.value F W t x/Expr.value F W t y := by rw [div_eq_mul_inv];rfl

theorem eval_coeff {d : ℕ} (φ : ℝ → ℝ) (t : Fin d → ℝ) (p : Expr d) (m : Regime) :
    eval φ t (coefficients m p).beta=(realCoeff m φ (eval φ t p)).beta ∧
    eval φ t (coefficients m p).a=(realCoeff m φ (eval φ t p)).a ∧
    eval φ t (coefficients m p).b=(realCoeff m φ (eval φ t p)).b := by
  cases m <;> simp [coefficients,realCoeff,eval,atoms,value_sub,value_div,Expr.value,betaLP,etaLP,prim,
    PaperMiddle.canonical,PaperMiddle.eps,div_eq_mul_inv,sub_eq_add_neg] <;> norm_num

theorem eval_add {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    eval F t (x+y)=eval F t x+eval F t y := rfl
theorem eval_sub {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    eval F t (x-y)=eval F t x-eval F t y := rfl
theorem eval_mul {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    eval F t (x*y)=eval F t x*eval F t y := rfl
theorem eval_neg {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x : Expr d) :
    eval F t (-x)= -eval F t x := rfl
theorem eval_div {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x y : Expr d) :
    eval F t (x/y)=eval F t x/eval F t y := by rw [div_eq_mul_inv];rfl
theorem eval_lam {d} (F : ℝ → ℝ) (t : Fin d → ℝ) : eval F t familyExprLam=PaperMiddle.lam := by
  dsimp [eval,familyExprLam,PaperMiddle.lam,Expr.value];norm_num
theorem eval_rc {d} (F : ℝ → ℝ) (t : Fin d → ℝ) : eval F t familyExprRc=PaperMiddle.rc := by
  dsimp [eval,familyExprRc,PaperMiddle.rc,Expr.value];norm_num
theorem eval_one {d} (F : ℝ → ℝ) (t : Fin d → ℝ) : eval F t (1 : Expr d)=1 := by
  change ((1:ℚ):ℝ)=1;norm_num
theorem eval_phi {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x : Expr d) : eval F t (phi x)=F (eval F t x) := rfl
theorem eval_J {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x : Expr d) : eval F t (prim x)=J F (eval F t x) := rfl
theorem eval_coord {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (i : Fin d) : eval F t (.coord i)=t i := rfl
theorem eval_pos {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (x : Expr d) : eval F t x.pos=max (eval F t x) 0 := rfl
theorem eval_potential {d} (F : ℝ → ℝ) (t : Fin d → ℝ) (r y : Expr d) :
    eval F t (.potential r y)=potential PaperMiddle.lam F (eval F t r) (eval F t y) := rfl

theorem eval_third {d : ℕ} (φ : ℝ → ℝ) (m : Regime) (t : Fin d → ℝ) (p q r : Expr d) :
    let c := realCoeff m φ (eval φ t p)
    eval φ t (third p q r (coefficients m p)) =
      highFirst PaperMiddle.lam φ c.beta c.a c.b (eval φ t p) (eval φ t q) (eval φ t r) := by
  obtain ⟨hB,ha,hb⟩ := eval_coeff φ t p m
  simp only [third,eval_add,eval_sub,eval_mul,eval_neg,eval_one,eval_phi,eval_J,
    eval_pos,eval_potential,eval_lam,hB,ha,hb,highFirst,deltaP]

theorem eval_fourth {d : ℕ} (φ : ℝ → ℝ) (m : Regime) (t : Fin d → ℝ) (p q z r : Expr d) :
    let c := realCoeff m φ (eval φ t p)
    eval φ t (fourth p q z r (coefficients m p)) =
      highSecond PaperMiddle.lam φ c.beta c.a c.b (eval φ t p) (eval φ t q) (eval φ t z) (eval φ t r) := by
  obtain ⟨hB,ha,hb⟩ := eval_coeff φ t p m
  simp only [fourth,eval_add,eval_sub,eval_mul,eval_neg,eval_one,eval_phi,eval_J,
    eval_pos,eval_potential,eval_lam,hB,ha,hb,highSecond,KP]


theorem expression_correct (φ : ℝ → ℝ) (m : Regime) (s : Side) (k : Family) (t : Fin k.dim → ℝ) :
    eval φ t (expression m s k)=target m s φ k t := by
  have hB {d : ℕ} (t : Fin d → ℝ) (p : Expr d) := (eval_coeff φ t p m).1
  have ha {d : ℕ} (t : Fin d → ℝ) (p : Expr d) := (eval_coeff φ t p m).2.1
  have hb {d : ℕ} (t : Fin d → ℝ) (p : Expr d) := (eval_coeff φ t p m).2.2
  cases k <;> cases s <;>
    simp only [expression,target,first,second,third,fourth,getRatio,eval_add,eval_sub,eval_mul,eval_neg,
      eval_div,eval_lam,eval_rc,eval_one,eval_phi,eval_J,eval_pos,eval_potential,hB,ha,hb,eval_coord,
      lowFirst,lowSecond,highFirst,highSecond,correction,ratio,deltaP,KP]


def BoxBound (φ : ℝ → ℝ) (m : Regime) (s : Side) (k : Family) (p : ℝ) : Prop :=
  ∀ x : Fin k.dim → ℝ, (∀ i, i.val=0 → x i=p) → (∀ i,0 < i.val → x i∈Icc 0 1) →
    eval φ x (expression m s k)≤0


def Needed (p : ℝ) (k : Family) : Prop := k=.L2 → p≤PaperMiddle.lam


structure MiddleBoxes (φ : ℝ → ℝ) : Prop where
  constant : ∀ p ∈ Icc PaperMiddle.p0 PaperMiddle.pA,∀ k,Needed p k → BoxBound φ .constant .below k p
  lpBelow : ∀ p ∈ Icc PaperMiddle.pA PaperMiddle.lam,∀ k,Needed p k → BoxBound φ .lp .below k p
  lpAbove : ∀ p ∈ Ioc PaperMiddle.lam PaperMiddle.pC,∀ k,Needed p k → BoxBound φ .lp .above k p
  canonical : ∀ p ∈ Icc PaperMiddle.pC PaperMiddle.p1,∀ k,Needed p k → BoxBound φ .canonical .above k p

structure RemainingBoxes (φ : ℝ → ℝ) : Prop where
  lpBelow : ∀ p ∈ Ioc PaperMiddle.pA PaperMiddle.lam,∀ k,Needed p k → BoxBound φ .lp .below k p
  lpAbove : ∀ p ∈ Ioc PaperMiddle.lam PaperMiddle.pC,∀ k,Needed p k → BoxBound φ .lp .above k p
  canonical : ∀ p ∈ Ioc PaperMiddle.pC PaperMiddle.p1,∀ k,Needed p k → BoxBound φ .canonical .above k p

end
end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Set
noncomputable section


private theorem affine_ends {s t k b : ℝ} (hs : k*s+b ≤ 0) (ht : k*t+b ≤ 0)
    (r : ℝ) (hr : r∈Icc s t) : k*r+b ≤ 0 := by
  rcases le_total 0 k with hk|hk
  · linarith only [mul_le_mul_of_nonneg_left hr.2 hk,ht]
  · linarith only [mul_le_mul_of_nonpos_left hr.1 hk,hs]


theorem clipped_affine_ends {s t k d m a b : ℝ}
    (check : ∀ r ∈ Icc s t, r=s ∨ r=t ∨ a*r+b=0 → k*r+d-m*max (a*r+b) 0 ≤ 0) :
    ∀ r ∈ Icc s t, k*r+d-m*max (a*r+b) 0 ≤ 0 := by
  intro r hr
  have hst := hr.1.trans hr.2
  have ends := check s ⟨le_rfl,hst⟩ (Or.inl rfl)
  have endt := check t ⟨hst,le_rfl⟩ (Or.inr (Or.inl rfl))
  have segment (u v : ℝ) (hru : r∈Icc u v)
      (hu : k*u+d-m*max (a*u+b) 0 ≤ 0) (hv : k*v+d-m*max (a*v+b) 0 ≤ 0)
      (sign : (a*u+b ≤ 0 ∧ a*v+b ≤ 0) ∨ (0 ≤ a*u+b ∧ 0 ≤ a*v+b)) :
      k*r+d-m*max (a*r+b) 0 ≤ 0 := by
    rcases sign with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · have h := affine_ends h₁ h₂ r hru
      simpa only [max_eq_right h,mul_zero,sub_zero] using affine_ends
        (by simpa only [max_eq_right h₁,mul_zero,sub_zero] using hu : k*u+d ≤ 0)
        (by simpa only [max_eq_right h₂,mul_zero,sub_zero] using hv : k*v+d ≤ 0) r hru
    · have hn : 0 ≤ a*r+b := by
        rcases le_total 0 a with h|h
        · linarith only [h₁,mul_le_mul_of_nonneg_left hru.1 h]
        · linarith only [h₂,mul_le_mul_of_nonpos_left hru.2 h]
      rw [max_eq_left h₁] at hu
      rw [max_eq_left h₂] at hv
      rw [max_eq_left hn]
      have h₃ : (k-m*a)*u+(d-m*b) ≤ 0 := by linarith only [hu]
      have h₄ : (k-m*a)*v+(d-m*b) ≤ 0 := by linarith only [hv]
      linarith only [affine_ends h₃ h₄ r hru]
  by_cases h₁ : a*s+b ≤ 0
  · by_cases h₂ : a*t+b ≤ 0
    · exact segment s t hr ends endt (Or.inl ⟨h₁,h₂⟩)
    have h₂' := le_of_not_ge h₂
    obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc hst (f:=fun w : ℝ => a*w+b)
      (continuous_const.mul continuous_id |>.add continuous_const |>.continuousOn) (show (0:ℝ)∈Icc _ _ from ⟨h₁,h₂'⟩)
    have bound := check c hc (Or.inr (Or.inr hzero))
    rcases le_total r c with h|h
    · exact segment s c ⟨hr.1,h⟩ ends bound (Or.inl ⟨h₁,hzero.le⟩)
    · exact segment c t ⟨h,hr.2⟩ bound endt (Or.inr ⟨hzero.ge,h₂'⟩)
  · have h₁' := le_of_not_ge h₁
    by_cases h₂ : 0 ≤ a*t+b
    · exact segment s t hr ends endt (Or.inr ⟨h₁',h₂⟩)
    have h₂' := le_of_not_ge h₂
    obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc' hst (f:=fun w : ℝ => a*w+b)
      (continuous_const.mul continuous_id |>.add continuous_const |>.continuousOn) (show (0:ℝ)∈Icc _ _ from ⟨h₂',h₁'⟩)
    have bound := check c hc (Or.inr (Or.inr hzero))
    rcases le_total r c with h|h
    · exact segment s c ⟨hr.1,h⟩ ends bound (Or.inr ⟨h₁',hzero.ge⟩)
    · exact segment c t ⟨h,hr.2⟩ bound endt (Or.inl ⟨hzero.le,h₂'⟩)

theorem potential_affine (lam : ℝ) (φ : ℝ → ℝ) (y : ℝ) :
    ∃ k d, ∀ r, potential lam φ r y = k*r+d := by
  by_cases h : y ≤ lam
  · exact ⟨0,0,by simp [potential,h]⟩
  · exact ⟨-φ y,lam-y,fun r => by simp only [potential,if_neg h]; ring⟩

theorem highFirst_ends (lam : ℝ) (φ : ℝ → ℝ) (β a b p q s t : ℝ)
    (hc : ∀ r ∈ Icc s t, r=s ∨ r=t ∨ a*r+b=0 → highFirst lam φ β a b p q r ≤ 0) :
    ∀ r ∈ Icc s t, highFirst lam φ β a b p q r ≤ 0 := by
  obtain ⟨k,d,h⟩ := potential_affine lam φ q
  have eqn (r : ℝ) : highFirst lam φ β a b p q r =
      k*r+(q+β*deltaP φ p q+d-lam) - max (-φ q) 0*max (a*r+b) 0 := by
    rw [highFirst,h]; ring
  simpa only [eqn] using (clipped_affine_ends (fun r hr hk => by
    simpa only [eqn] using hc r hr hk))

theorem highSecond_ends (lam : ℝ) (φ : ℝ → ℝ) (β a b p q z s t : ℝ)
    (hc : ∀ r ∈ Icc s t, r=s ∨ r=t ∨ a*r+b=0 → highSecond lam φ β a b p q z r ≤ 0) :
    ∀ r ∈ Icc s t, highSecond lam φ β a b p q z r ≤ 0 := by
  obtain ⟨k,d,h⟩ := potential_affine lam φ q
  obtain ⟨k',d',h'⟩ := potential_affine lam φ z
  have eqn (r : ℝ) : highSecond lam φ β a b p q z r =
      (k-k')*r+(q+β*KP φ p q z+d-d') - max (-φ z) 0*max (a*r+b) 0 := by
    rw [highSecond,h,h']; ring
  simpa only [eqn] using (clipped_affine_ends (fun r hr hk => by
    simpa only [eqn] using hc r hr hk))

end
end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Set


structure ReducedBounds (lam R : ℝ) (φ : ℝ → ℝ) (β a b p : ℝ) : Prop where
  low₁ : ∀ q ∈ Icc 0 (min p lam), ∀ x ∈ Icc q lam, lowFirst lam φ β a b p q x ≤ 0
  low₂ : p ≤ lam → ∀ q ∈ Icc 0 p, ∀ x ∈ Icc p lam, lowSecond lam φ β a b p q x ≤ 0
  high₁ : ∀ q ∈ Icc 0 p, ∀ r ∈ Icc 1 R, r=1 ∨ r=R ∨ a*r+b=0 →
    highFirst lam φ β a b p q r ≤ 0
  high₂ : ∀ q ∈ Icc 0 p, ∀ z ∈ Icc p 1, ∀ r ∈ Icc 1 R, r=1 ∨ r=R ∨ a*r+b=0 →
    highSecond lam φ β a b p q z r ≤ 0

theorem reduced_implies_cubes {lam rc R β a b p : ℝ} {φ : ℝ → ℝ}
    (hp : p∈Icc 0 1) (hl : 0≤lam) (hrc : 0≤rc) (hR : 1≤R)
    (range : ∀ x ∈ Icc 0 rc, ratio lam φ x ∈ Icc 1 R) (h : ReducedBounds lam R φ β a b p) :
    CubeBounds lam rc φ β a b p := by
  have scale {u l : ℝ} (hu : u∈Icc 0 1) (hh : 0≤l) : u*l ∈ Icc 0 l :=
    ⟨mul_nonneg hu.1 hh, by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu.2 hh⟩
  have shift {v l u : ℝ} (hv : v∈Icc 0 1) (hlu : l≤u) : l+v*(u-l)∈Icc l u := by
    have ht := scale hv (sub_nonneg.mpr hlu)
    exact ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
  have hr₀ : (1:ℝ)∈Icc 1 R := ⟨le_rfl,hR⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro u hu w hw
    have hq := scale hu (le_min hp.1 hl)
    exact h.low₁ _ hq _ (shift hw (hq.2.trans (min_le_right _ _)))
  · intro hpl u hu w hw
    exact h.low₂ hpl _ (scale hu hp.1) _ (shift hw hpl)
  · intro u hu w hw
    exact highFirst_ends _ _ _ _ _ _ _ _ _ (h.high₁ _ (scale hu hp.1)) _ (range _ (scale hw hrc))
  · intro u hu
    exact h.high₁ _ (scale hu hp.1) 1 hr₀ (Or.inl rfl)
  · intro u hu v hv w hw
    exact highSecond_ends _ _ _ _ _ _ _ _ _ _ (h.high₂ _ (scale hu hp.1) _ (shift hv hp.2)) _
      (range _ (scale hw hrc))
  · intro u hu v hv
    exact h.high₂ _ (scale hu hp.1) _ (shift hv hp.2) 1 hr₀ (Or.inl rfl)

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open Set PaperBox
noncomputable section

inductive KnotCase | one | maximum | corner deriving DecidableEq, Repr


def ratioExpr {d : ℕ} (mode : Regime) (R : ℚ) (p : Expr d) : KnotCase → Expr d
  | .one => .const 1
  | .maximum => .const R
  | .corner => .mul (.neg (coefficients mode p).b) (.inv (coefficients mode p).a)

def ratioValue (m : Regime) (φ : ℝ → ℝ) (R : ℚ) (p : ℝ) : KnotCase → ℝ
  | .one => 1
  | .maximum => R
  | .corner => -(realCoeff m φ p).b/(realCoeff m φ p).a

theorem eval_ratioExpr {d : ℕ} (φ : ℝ → ℝ) (m : Regime) (R : ℚ) (p : Expr d)
    (t : Fin d → ℝ) (v : KnotCase) : eval φ t (ratioExpr m R p v)=ratioValue m φ R (eval φ t p) v := by
  obtain ⟨_,ha,hb⟩ := eval_coeff φ t p m
  cases v with
  | one => change ((1:ℚ):ℝ)=1;norm_num
  | maximum => rfl
  | corner =>
    change -eval φ t (coefficients m p).b * (eval φ t (coefficients m p).a)⁻¹=_
    rw [ha,hb];rfl

def reducedFirst (m : Regime) (R : ℚ) (k : KnotCase) : Expr 2 :=
  let p := Expr.coord 0
  third p (.mul (.coord 1) p) (ratioExpr m R p k) (coefficients m p)

def reducedSecond (m : Regime) (R : ℚ) (k : KnotCase) : Expr 3 :=
  let p := Expr.coord 0
  let z := Expr.add p (.mul (.coord 2) (.add (.const 1) (.neg p)))
  fourth p (.mul (.coord 1) p) z (ratioExpr m R p k) (coefficients m p)

theorem eval_reducedFirst (φ : ℝ → ℝ) (m : Regime) (R : ℚ) (k : KnotCase) (p u : ℝ) :
    let c := realCoeff m φ p
    eval φ ![p,u] (reducedFirst m R k) =
      highFirst PaperMiddle.lam φ c.beta c.a c.b p (u*p) (ratioValue m φ R p k) := by
  rw [reducedFirst,eval_third,eval_ratioExpr]
  rfl

theorem eval_reducedSecond (φ : ℝ → ℝ) (m : Regime) (R : ℚ) (k : KnotCase) (p u v : ℝ) :
    let c := realCoeff m φ p
    eval φ ![p,u,v] (reducedSecond m R k) =
      highSecond PaperMiddle.lam φ c.beta c.a c.b p (u*p) (p+v*(1-p)) (ratioValue m φ R p k) := by
  rw [reducedSecond,eval_fourth,eval_ratioExpr]
  change highSecond _ _ _ _ _ _ _ (p+v*(((1:ℚ):ℝ)+ -p)) _=_
  norm_num [sub_eq_add_neg] <;> rfl


structure ReducedBoxes (φ : ℝ → ℝ) (m : Regime) (s : Side) (R : ℚ) (p : ℝ) : Prop where
  low₁ : BoxBound φ m s .L1 p
  low₂ : p≤PaperMiddle.lam → BoxBound φ m s .L2 p
  high₁ : ∀ k,ratioValue m φ R p k∈Icc 1 (R:ℝ) →
    ∀ u ∈ Icc 0 1,eval φ ![p,u] (reducedFirst m R k)≤0
  high₂ : ∀ k,ratioValue m φ R p k∈Icc 1 (R:ℝ) →
    ∀ u ∈ Icc 0 1,∀ v ∈ Icc 0 1,eval φ ![p,u,v] (reducedSecond m R k)≤0

theorem reduced_of_boxes {φ : ℝ → ℝ} {m : Regime} {s : Side} {p : ℝ} {R : ℚ}
    (hs : match s with | .below => p≤PaperMiddle.lam | .above => PaperMiddle.lam≤p)
    (h : ReducedBoxes φ m s R p) :
    let c := realCoeff m φ p
    ReducedBounds PaperMiddle.lam R φ c.beta c.a c.b p := by
  let c := realCoeff m φ p
  have hq : (match s with | .below => p | .above => PaperMiddle.lam)=min p PaperMiddle.lam := by
    cases s <;> simp_all
  have knot (r : ℝ) (hr : r=1 ∨ r=(R:ℝ) ∨ c.a*r+c.b=0) :
      ∃ k : KnotCase,ratioValue m φ R p k=r := by
    rcases hr with hr|hr|hr
    · exact ⟨.one,hr.symm⟩
    · exact ⟨.maximum,hr.symm⟩
    · have ha : c.a≠0 := by cases m <;> norm_num [c,realCoeff]
      exact ⟨.corner,(div_eq_iff ha).mpr (by change -c.b=r*c.a;linarith only [hr,show r*c.a=c.a*r by ring])⟩
  constructor
  · intro q hq' x hx
    obtain ⟨u,hu,he⟩ := affine_parameter (lo:=0) hq'
    obtain ⟨w,hw,hw'⟩ := affine_parameter hx
    simp only [zero_add,sub_zero] at he
    have hh := h.low₁ ![p,u,w] (by intro i;fin_cases i <;> simp) (by intro i;fin_cases i <;> simp [hu,hw])
    rw [expression_correct φ m s .L1 ![p,u,w]] at hh
    cases s with
    | below =>
      change lowFirst _ _ _ _ _ p (u*p) (u*p+w*(PaperMiddle.lam-u*p))≤0 at hh
      rw [min_eq_left hs] at he
      rwa [← he,← hw'] at hh
    | above =>
      change lowFirst _ _ _ _ _ p (u*PaperMiddle.lam) (u*PaperMiddle.lam+w*(PaperMiddle.lam-u*PaperMiddle.lam))≤0 at hh
      rw [min_eq_right hs] at he
      rwa [← he,← hw'] at hh
  · intro hpl q hq' x hx
    obtain ⟨u,hu,he⟩ := affine_parameter (lo:=0) hq'
    obtain ⟨w,hw,hw'⟩ := affine_parameter hx
    simp only [zero_add,sub_zero] at he
    have hh := h.low₂ hpl ![p,u,w] (by intro i;fin_cases i <;> simp) (by intro i;fin_cases i <;> simp [hu,hw])
    rw [expression_correct φ m s .L2 ![p,u,w]] at hh
    change lowSecond _ _ _ _ _ p (u*p) (p+w*(PaperMiddle.lam-p))≤0 at hh
    rwa [← he,← hw'] at hh
  · intro q hq' r hr hk
    obtain ⟨u,hu,he⟩ := affine_parameter (lo:=0) hq'
    simp only [zero_add,sub_zero] at he
    obtain ⟨k,hk⟩ := knot r hk
    have hh := h.high₁ k (by rw [hk];exact hr) u hu
    rwa [eval_reducedFirst,hk,← he] at hh
  · intro q hq' z hz r hr hk
    obtain ⟨u,hu,he⟩ := affine_parameter (lo:=0) hq'
    obtain ⟨v,hv,he'⟩ := affine_parameter hz
    simp only [zero_add,sub_zero] at he
    obtain ⟨k,hk⟩ := knot r hk
    have hh := h.high₂ k (by rw [hk];exact hr) u hu v hv
    rwa [eval_reducedSecond,hk,← he,← he'] at hh


structure ReducedRanges (φ : ℝ → ℝ) (R : ℚ) : Prop where
  lpBelow : ∀ p∈Ioc PaperMiddle.pA PaperMiddle.lam,ReducedBoxes φ .lp .below R p
  lpAbove : ∀ p∈Ioc PaperMiddle.lam PaperMiddle.pC,ReducedBoxes φ .lp .above R p
  canonical : ∀ p∈Ioc PaperMiddle.pC PaperMiddle.p1,ReducedBoxes φ .canonical .above R p

theorem cubes_of_reduced_ranges {φ : ℝ → ℝ} {R : ℚ} (h : ReducedRanges φ R)
    (hR : (1:ℝ)≤R) (hr : ∀ x ∈ Icc 0 PaperMiddle.rc,ratio PaperMiddle.lam φ x∈Icc 1 (R:ℝ))
    {p : ℝ} (hp : p∈Ioc PaperMiddle.pA PaperMiddle.p1) :
    CubeBounds PaperMiddle.lam PaperMiddle.rc φ (PaperMiddle.beta φ p) (PaperMiddle.a p) (PaperMiddle.b φ p) p := by
  have hp01 : p∈Icc (0:ℝ) 1 := ⟨(by norm_num [PaperMiddle.pA] : (0:ℝ)≤PaperMiddle.pA).trans hp.1.le,
    hp.2.trans (by norm_num [PaperMiddle.p1])⟩
  have hc (m : Regime) (s : Side)
      (hs : match s with | .below => p≤PaperMiddle.lam | .above => PaperMiddle.lam≤p)
      (hrd : ReducedBoxes φ m s R p) :=
    reduced_implies_cubes (rc:=PaperMiddle.rc) hp01 (by norm_num [PaperMiddle.lam]) (by norm_num [PaperMiddle.rc])
      hR hr (reduced_of_boxes hs hrd)
  have ha := not_le.mpr hp.1
  by_cases hpc : p≤PaperMiddle.pC
  · by_cases hl : p≤PaperMiddle.lam
    · have hh := hc .lp .below hl (h.lpBelow p ⟨hp.1,hl⟩)
      simpa [realCoeff,PaperMiddle.beta,PaperMiddle.a,PaperMiddle.b,ha,hpc] using hh
    · have hh := hc .lp .above (le_of_not_ge hl) (h.lpAbove p ⟨lt_of_not_ge hl,hpc⟩)
      simpa [realCoeff,PaperMiddle.beta,PaperMiddle.a,PaperMiddle.b,ha,hpc] using hh
  · have hlf : PaperMiddle.lam≤p := (show PaperMiddle.lam≤PaperMiddle.pC by norm_num [PaperMiddle.lam,PaperMiddle.pC]).trans (le_of_not_ge hpc)
    have hh := hc .canonical .above hlf (h.canonical p ⟨lt_of_not_ge hpc,hp.2⟩)
    simpa [realCoeff,PaperMiddle.beta,PaperMiddle.a,PaperMiddle.b,ha,hpc,hp.2] using hh

end
end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem gPhi_properties {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ) :
    ϕ lam = 0 ∧ (∀ r ∈ Set.Icc lam 1, ϕ r ≤ 0) ∧ IsActivation (gPhi ϕ) ∧
      gPhi ϕ 0 = 0 ∧ gPhi ϕ 1 = 1 ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r = (1 + ϕ 0) * ((∫ u in (0 : ℝ)..1, gPhi ϕ u) - gPhi ϕ r) := by
  have hl : lam ∈ Icc 0 1 := ⟨h.lam_mem.1.le,h.lam_mem.2.le⟩
  have h0 : 0 < ϕ 0 := h.pos 0 ⟨le_rfl,h.lam_mem.1⟩
  have hd : 0 < 1+ϕ 0 := by linarith
  have hpt : MapsTo ϕ (Ico 0 lam) (Ici 0) := fun x hx => (h.pos x hx).le
  have hc : ContinuousOn ϕ (closure (Ico 0 lam)) := by
    rw [closure_Ico h.lam_mem.1.ne]
    exact h.continuousOn.mono (Icc_subset_Icc le_rfl hl.2)
  have hclosed := hpt.closure_of_continuousOn hc
  rw [closure_Ico h.lam_mem.1.ne, isClosed_Ici.closure_eq] at hclosed
  have hz : ϕ lam = 0 := le_antisymm (by linarith [h.le_lam_sub lam hl]) (hclosed ⟨hl.1,le_rfl⟩)
  have hm : MonotoneOn (gPhi ϕ) (Icc 0 1) := by
    intro x hx y hy hxy
    apply div_le_div_of_nonneg_right _ hd.le
    linarith [h.antitoneOn hx hy hxy]
  have hz0 : gPhi ϕ 0=0 := by simp [gPhi]
  have hz1 : gPhi ϕ 1=1 := by
    rw [gPhi,h.at_one,sub_neg_eq_add,add_comm (ϕ 0) 1,div_self hd.ne']
  have hi := h.continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ)≤1)
  have hmean : (∫ u in (0:ℝ)..1, gPhi ϕ u) = ϕ 0/(1+ϕ 0) := by
    simp only [gPhi]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (f := fun _ => ϕ 0)
      (g := ϕ) intervalIntegrable_const hi, h.integral_eq_zero, intervalIntegral.integral_const]
    simp
  refine ⟨hz,fun r hr => ?_, ⟨?_,hm,?_⟩,hz0,hz1,fun r _ => ?_⟩
  · rw [← hz]; exact h.antitoneOn hl ⟨hl.1.trans hr.1,hr.2⟩ hr.1
  · exact (continuousOn_const.sub h.continuousOn).div_const _
  · intro z hz
    exact ⟨hz0 ▸ hm (by norm_num) hz hz.1,hz1 ▸ hm hz (by norm_num) hz.2⟩
  · rw [hmean,gPhi]
    field_simp [hd.ne'] <;> ring

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open Set PaperCurve PaperBox PaperFamilies


theorem ratio_antitone : AntitoneOn (ratio lam score) (Ico 0 lam) := by
  intro x hx y hy hxy
  apply antitone_rows data_chain (show (startKnot.x:ℝ) ≤ x by simpa [startKnot] using hx.1)
    (show y ≤ (endKnot.x:ℝ) from by simpa [endKnot] using (hy.2.trans_le score_isScoreFunction.lam_mem.2.le).le) hxy
  intro p hp s t hps hst htp hxs hty
  have eq (v : ℝ) (hv : v∈Icc s t) : score v=p.value v := score_on_piece hp ⟨hps.trans hv.1,hv.2.trans htp⟩
  have h := ratio_row (data_valid p hp).1 (data_ratios p hp) hps hst htp (hty.trans_lt hy.2) (fun v hv =>
    (eq v hv) ▸ score_isScoreFunction.pos v ⟨(hx.1.trans hxs).trans hv.1,(hv.2.trans hty).trans_lt hy.2⟩)
  simpa only [ratio,eq s ⟨le_rfl,hst⟩,eq t ⟨hst,le_rfl⟩] using h


theorem canonical_low_redundant {p β q x : ℝ} (hp : p ∈ Icc 0 1) (hβ : 0 ≤ β)
    (hq : q∈Icc 0 (min p lam)) (hx : x∈Icc q lam)
    (hh : highFirst lam score β 1 (-(β*(1-p))) p q 1 ≤ 0) :
    lowFirst lam score β 1 (-(β*(1-p))) p q x ≤ 0 := by
  let t := β*(1-p)
  have qL := hq.2.trans (min_le_right _ _)
  have hqφ : 0 ≤ score q := by
    rcases qL.lt_or_eq with h|rfl
    · exact (score_isScoreFunction.pos q ⟨hq.1,h⟩).le
    · rw [(gPhi_properties score_isScoreFunction).1]
  have hbase : q+β*deltaP score p q ≤ lam := by
    simpa [highFirst,potential,if_pos qL,max_eq_right (neg_nonpos.mpr hqφ),sub_nonpos] using hh
  have hb := mul_le_mul_of_nonneg_left ((eq_43_44 score_isScoreFunction).1 p q hq.1 (hq.2.trans (min_le_left _ _)) hp.2).2.1 hβ
  change q+β*deltaP score p q+max (1*(lam-x)+(-t)*score x) 0-lam ≤ 0
  by_cases hc : 1*(lam-x)+(-t)*score x ≤ 0
  · rw [max_eq_right hc];linarith
  rw [max_eq_left (le_of_not_ge hc)]
  have hxL : x<lam := lt_of_le_of_ne hx.2 (fun he => by
    subst x;rw [(gPhi_properties score_isScoreFunction).1] at hc;simp at hc)
  have hx' : x∈Ico (0:ℝ) lam := ⟨hq.1.trans hx.1,hxL⟩
  have hq' : q∈Ico (0:ℝ) lam := ⟨hq.1,hx.1.trans_lt hxL⟩
  have hxpos := score_isScoreFunction.pos x hx'
  have hqpos := score_isScoreFunction.pos q hq'
  have hrat := ratio_antitone hq' hx' hx.1
  have hR (a : ℝ) (ha : 0 < score a) : score a*(ratio lam score a)=lam-a := by unfold ratio;field_simp
  have hs := score_isScoreFunction.antitoneOn ⟨hq.1,qL.trans score_isScoreFunction.lam_mem.2.le⟩
    ⟨hx'.1,hx.2.trans score_isScoreFunction.lam_mem.2.le⟩ hx.1
  have hxr : t ≤ ratio lam score x := (le_div_iff₀ hxpos).mpr (by linarith)
  have hbound := mul_le_mul hs (sub_le_sub_right hrat t) (sub_nonneg.mpr hxr) hqpos.le
  dsimp [t] at *
  nlinarith only [hbound,hR q hqpos,hR x hxpos,hb]


theorem canonical_L1_of_highFirst {p : ℝ} (hp : p∈Icc PaperMiddle.pC PaperMiddle.p1) (R : ℚ)
    (hhigh : ∀ u∈Icc (0:ℝ) 1,eval score ![p,u] (reducedFirst .canonical R .one) ≤ 0) :
    BoxBound score .canonical .above .L1 p := by
  have hLam : PaperMiddle.lam=lam := by norm_num [PaperMiddle.lam,lam,lamQ]
  have hpL : lam ≤ p := (by norm_num [PaperMiddle.pC,lam,lamQ] : lam ≤ PaperMiddle.pC).trans hp.1
  have hp' : p∈Icc (0:ℝ) 1 := ⟨score_isScoreFunction.lam_mem.1.le.trans hpL,
    hp.2.trans (by norm_num [PaperMiddle.p1])⟩
  have hJ : 0 ≤ J score p := by
    have h := primitive_decreases ⟨hpL,hp'.2⟩ ⟨score_isScoreFunction.lam_mem.2.le,le_rfl⟩ hp'.2
    rwa [show J score 1=0 from score_isScoreFunction.integral_eq_zero] at h
  have hβ : 0 ≤ PaperMiddle.canonical score p := by unfold PaperMiddle.canonical PaperMiddle.eps;positivity [hp'.1]
  intro z hz hi
  have h₀ := hz 0 rfl
  have hu := hi 1 (by decide)
  have hw := hi 2 (by decide)
  let q := z 1*lam
  have hq : q∈Icc (0:ℝ) lam := ⟨mul_nonneg hu.1 score_isScoreFunction.lam_mem.1.le,
    by simpa [q] using mul_le_mul_of_nonneg_right hu.2 score_isScoreFunction.lam_mem.1.le⟩
  have hqp := hq.2.trans hpL
  obtain ⟨u,hu',he⟩ := affine_parameter (lo:=0) (show q∈Icc (0:ℝ) p from ⟨hq.1,hqp⟩)
  simp only [zero_add,sub_zero] at he
  have high := hhigh u hu'
  rw [eval_reducedFirst] at high
  change highFirst PaperMiddle.lam score _ 1 _ p (u*p) 1 ≤ 0 at high
  rw [hLam,← he] at high
  rw [expression_correct]
  change lowFirst PaperMiddle.lam score (PaperMiddle.canonical score (z 0)) 1 (-(PaperMiddle.canonical score (z 0)*(1-z 0)))
    (z 0) (z 1*PaperMiddle.lam) (z 1*PaperMiddle.lam+z 2*(PaperMiddle.lam-z 1*PaperMiddle.lam)) ≤ 0
  rw [hLam,h₀]
  apply canonical_low_redundant hp' hβ ⟨hq.1,le_min hqp hq.2⟩ _ high
  exact ⟨by linarith only [mul_nonneg hw.1 (sub_nonneg.mpr hq.2)],by
    nlinarith only [mul_le_mul_of_nonneg_right hw.2 (sub_nonneg.mpr hq.2)]⟩

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set
end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory


theorem concave_increment_antitone {lam : ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc lam 1) f)
    {x y s : ℝ} (hx : lam ≤ x) (hxy : x ≤ y) (hs : 0 ≤ s) (hy : y+s ≤ 1) :
    f (y+s)-f y ≤ f (x+s)-f x := by
  rcases hs.eq_or_lt with rfl | hpos
  · simp
  let T := y+s-x
  have hT : 0<T := by dsimp [T]; linarith
  let u := s/T
  have hue : u*T=s := div_mul_cancel₀ _ hT.ne'
  have hu : 0 ≤ u := div_nonneg hpos.le hT.le
  have hv : 0 ≤ 1-u := sub_nonneg.mpr ((div_le_one hT).mpr (by dsimp [T]; linarith))
  have hxm : x ∈ Icc lam 1 := ⟨hx,by linarith⟩
  have hym : y+s ∈ Icc lam 1 := ⟨by linarith,hy⟩
  have h1 := hf.2 hxm hym hv hu (by ring)
  have h2 := hf.2 hxm hym hu hv (by ring)
  simp only [smul_eq_mul] at h1 h2
  dsimp only [T] at hue
  have hx' : (1-u)*x+u*(y+s)=x+s := by nlinarith only [hue]
  have hy' : u*x+(1-u)*(y+s)=y := by nlinarith only [hue]
  rw [hx'] at h1; rw [hy'] at h2
  linarith only [h1,h2]


theorem J_increment {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a+s ≤ 1) :
    J ϕ (a+s)-J ϕ a = ∫ u in (0:ℝ)..s, ϕ (a+u) := by
  have ai {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :=
    (h.continuousOn.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc (μ := volume) hxy
  have had := intervalIntegral.integral_add_adjacent_intervals (ai (le_refl 0) ha (by linarith))
    (ai ha (by linarith : a ≤ a+s) has)
  unfold J
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero,zero_add] at *
  linarith

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory


theorem high_tail_penalty {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    (hconc : ConcaveOn ℝ (Icc lam 1) ϕ) (hadd : AntitoneOn (fun x => ϕ x+x) (Icc lam 1))
    {p q z B R penalty : ℝ} (hp : p ∈ Ioo lam 1) (hq : q ∈ Icc lam p) (hz : z ∈ Icc p 1)
    (hB : 0 ≤ B) (hBJ : p ≤ B*J ϕ p) (hR : 1 ≤ R)
    (hpen : 0 ≤ penalty) (hbase : z+B*KP ϕ p lam z+R*ϕ z-penalty ≤ 0)
    (hzero : ϕ lam=0) :
    z+B*KP ϕ p q z-R*(ϕ q-ϕ z)-penalty ≤ 0 := by
  let s := z-p
  have hs : 0 ≤ s := sub_nonneg.mpr hz.1
  have hsz : p+s=z := by dsimp [s];ring
  have hm (a : ℝ) (ha : a ∈ Icc lam p) : a+s ∈ Icc lam 1 := ⟨by linarith [ha.1],by linarith [ha.2,hz.2,hsz]⟩
  have hInt (a : ℝ) (ha : a ∈ Icc lam p) : IntervalIntegrable (fun u => ϕ (a+u)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs
    apply h.continuousOn.comp (f := fun u : ℝ => a+u) (by fun_prop)
    intro u hu
    exact ⟨by linarith [ha.1,h.lam_mem.1,hu.1],by linarith [ha.2,hu.2,hz.2,hsz]⟩
  have hK (a : ℝ) (ha : a ∈ Icc lam p) : KP ϕ p a z =
      (∫ u in (0:ℝ)..s, (ϕ (a+u)-ϕ (p+u))) - J ϕ p := by
    rw [intervalIntegral.integral_sub (hInt a ha) (hInt p ⟨hp.1.le,le_rfl⟩),
      ← J_increment h (h.lam_mem.1.le.trans ha.1) hs (hm a ha).2,
      ← J_increment h (h.lam_mem.1.le.trans hp.1.le) hs (by linarith [hsz,hz.2] : p+s ≤ 1), hsz]
    unfold KP
    rw [show a+s=z-p+a by dsimp [s];ring]
    ring
  let F := fun (a u : ℝ) => ϕ (a+u)-ϕ (p+u)
  have hFi (a : ℝ) (ha : a ∈ Icc lam p) : IntervalIntegrable (F a) volume 0 s := (hInt a ha).sub (hInt p ⟨hp.1.le,le_rfl⟩)
  by_cases hcut : B*s ≤ R
  · have hpoint (u : ℝ) (hu : u ∈ Icc 0 s) : F q u ≤ ϕ (q+s)-ϕ z := by
      have hi := concave_increment_antitone hconc (show lam ≤ q+u by linarith [hq.1,hu.1])
        (show q+u ≤ p+u by linarith [hq.2]) (show 0 ≤ s-u by linarith [hu.2]) (show p+u+(s-u) ≤ 1 by linarith [hsz,hz.2])
      rw [show q+u+(s-u)=q+s by ring,show p+u+(s-u)=z by linarith] at hi
      dsimp [F];linarith
    have hi := intervalIntegral.integral_mono_on hs (hFi q hq) (intervalIntegrable_const (c := ϕ (q+s)-ϕ z)) hpoint
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    have hqsz := h.antitoneOn ⟨h.lam_mem.1.le.trans (hm q hq).1,(hm q hq).2⟩
      ⟨by linarith [hq.1,h.lam_mem.1,hq.2,hz.1],hz.2⟩ (by linarith [hq.2,hsz] : q+s ≤ z)
    have hstrict := hadd ⟨hq.1,hq.2.trans hp.2.le⟩ (hm q hq) (by linarith : q ≤ q+s)
    dsimp only at hstrict
    have h1 := mul_le_mul_of_nonneg_left hi hB
    have h2 := mul_le_mul_of_nonneg_right hcut (sub_nonneg.mpr hqsz)
    have h3 := mul_le_mul_of_nonneg_left hstrict (zero_le_one.trans hR)
    have h4 := mul_le_mul_of_nonneg_right hR hs
    rw [hK q hq]
    change z+B*((∫ u in (0:ℝ)..s,F q u)-J ϕ p)-R*(ϕ q-ϕ z)-penalty ≤ 0
    nlinarith only [h1,h2,h3,h4,hBJ,hsz,hpen]
  · have hpoint (u : ℝ) (hu : u ∈ Icc 0 s) : F q u-F lam u ≤ ϕ q := by
      have hi := concave_increment_antitone hconc (le_refl lam) hq.1 hu.1
        (show q+u ≤ 1 by linarith [hu.2,hq.2,hsz,hz.2])
      rw [hzero] at hi
      dsimp [F];linarith
    have hla : lam ∈ Icc lam p := ⟨le_rfl,hp.1.le⟩
    have hi := intervalIntegral.integral_mono_on hs ((hFi q hq).sub (hFi lam hla))
      (intervalIntegrable_const (c := ϕ q)) hpoint
    rw [intervalIntegral.integral_sub (hFi q hq) (hFi lam hla),intervalIntegral.integral_const] at hi
    simp only [sub_zero,smul_eq_mul] at hi
    have hh := mul_le_mul_of_nonneg_left hi hB
    have hu := mul_le_mul_of_nonpos_right (le_of_not_ge hcut) ((gPhi_properties h).2.1 q ⟨hq.1,hq.2.trans hp.2.le⟩)
    rw [hK q hq]; rw [hK lam hla] at hbase
    change z+B*((∫ u in (0:ℝ)..s,F q u)-J ϕ p)-R*(ϕ q-ϕ z)-penalty ≤ 0
    change z+B*((∫ u in (0:ℝ)..s,F lam u)-J ϕ p)+R*ϕ z-penalty ≤ 0 at hbase
    nlinarith only [hh,hu,hbase]

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

private theorem large_tail {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {p q z M : ℝ} (hl : lam<p) (hp : p<1) (hq : q ∈ Icc 0 lam) (hz : z ∈ Icc p 1)
    (hM : 1 ≤ M) (hJ : 0 < J ϕ p) (h25 : Eq25 lam ϕ p)
    (hline : ϕ (lam+(1-p)) = -(1-p))
    (hLip : ∀ r s, p ≤ r → r<s → s ≤ 1 → ϕ r-ϕ s ≤ M*(s-r))
    (h47 : (M-1)*J ϕ p ≤ p*(1-(M+1)*(1-p))) :
    q+z-lam+(p/J ϕ p)*KP ϕ p q z+ϕ z ≤ 0 := by
  let B := p/J ϕ p
  have hp0 := h.lam_mem.1.trans hl
  have hB : 0 < B := div_pos hp0 hJ
  have hBJ : B*J ϕ p=p := div_mul_cancel₀ _ hJ.ne'
  have hEnd : q+B*deltaP ϕ p q ≤ lam := by
    have hh := h25 q hq.1 (le_min (hq.2.trans hl.le) hq.2)
    change p * deltaP ϕ p q ≤ (lam - q) * J ϕ p at hh
    have he : B*deltaP ϕ p q * J ϕ p = p*deltaP ϕ p q := by rw [mul_right_comm,hBJ]
    apply (le_of_mul_le_mul_right _ hJ)
    nlinarith only [he,hh]
  have hE1 : q+1-lam+B*KP ϕ p q 1+ϕ 1 ≤ 0 := by
    have hk : KP ϕ p q 1=deltaP ϕ p q := by simp [KP,deltaP,J,h.integral_eq_zero]
    rw [hk,h.at_one]; linarith
  by_cases hz1 : z=1
  · subst z; exact hE1
  let d := 1-z
  have hd : 0 < d := sub_pos.mpr (lt_of_le_of_ne hz.2 hz1)
  have ha : 0 ≤ z-p+q := by linarith [hz.1,hq.1]
  have hb : 1-p+q ≤ 1 := by linarith [hq.2]
  have hlineW : lam+(1-p) ≤ 1 := by linarith
  have hc := h.antitoneOn (show 1-p+q ∈ Icc 0 1 from ⟨by linarith [hq.1],hb⟩)
    (show lam+(1-p) ∈ Icc 0 1 from ⟨by linarith [h.lam_mem.1],hlineW⟩) (by linarith [hq.2])
  rw [hline] at hc
  have hlower := (primitive_sandwich h ha (show z-p+q ≤ 1-p+q by linarith [hz.2]) hb).1
  have hupper := (primitive_sandwich h (hp0.le.trans hz.1) hz.2 (le_refl 1)).2
  have hlip := hLip z 1 hz.1 (lt_of_le_of_ne hz.2 hz1) le_rfl
  have hzphi : ϕ z ≤ -1+M*(1-p) := by rw [h.at_one] at hlip; nlinarith [mul_le_mul_of_nonneg_left (show 1-z ≤ 1-p by linarith [hz.1]) (by linarith : 0 ≤ M)]
  have hcoef : 0 ≤ 1-M+B*(1-(M+1)*(1-p)) := by
    apply le_of_mul_le_mul_right _ hJ
    nlinarith only [h47,congrArg (fun x => x*(1-(M+1)*(1-p))) hBJ]
  have hk : d*(1-(M+1)*(1-p)) ≤ KP ϕ p q 1 - KP ϕ p q z := by
    unfold KP
    dsimp [d] at hd ⊢
    nlinarith only [hlower,hupper,mul_le_mul_of_nonneg_left hc hd.le,mul_le_mul_of_nonneg_left hzphi hd.le]
  change q+z-lam+B*KP ϕ p q z+ϕ z ≤ 0
  have hg := mul_nonneg hd.le hcoef
  have hk' := mul_le_mul_of_nonneg_left hk hB.le
  dsimp only [d] at hg hk'
  nlinarith only [hE1,hg,hk',hlip]

private theorem large_high_tail {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    (hconc : ConcaveOn ℝ (Icc lam 1) ϕ) (hadd : AntitoneOn (fun x => ϕ x+x) (Icc lam 1))
    {p q z B R : ℝ} (hp : p ∈ Ioo lam 1) (hq : q ∈ Icc lam p) (hz : z ∈ Icc p 1)
    (hB : 0 ≤ B) (hBJ : B*J ϕ p=p) (hR : 1 ≤ R)
    (hbase : lam+z-lam+B*KP ϕ p lam z+ϕ z ≤ 0)
    (hzero : ϕ lam=0) :
    z+B*KP ϕ p q z-R*(ϕ q-ϕ z) ≤ 0 := by
  have hzL := (gPhi_properties h).2.1 z ⟨hp.1.le.trans hz.1,hz.2⟩
  have hv := mul_le_mul_of_nonpos_right hR hzL
  have hh := high_tail_penalty h hconc hadd hp hq hz hB hBJ.ge hR (penalty:=0) le_rfl (by linarith) hzero
  simpa using hh

theorem lemma_14_ii {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p1 : ℝ} (hp1lam : lam < p1) (hp1 : p1 < 1)
    {rm zp : ℝ} (hrm0 : 0 ≤ rm) (hzp1 : zp ≤ 1) (hrm : rm < lam) (hzp : lam + (1 - p1) ≤ zp)
    (hline : ∀ r ∈ Set.Icc rm zp, ϕ r = lam - r)
    (hconc : ConcaveOn ℝ (Set.Icc lam 1) ϕ)
    {m0 M : ℝ} (hm0 : 0 < m0) (hm01 : m0 < 1) (hM : 1 ≤ M)
    (h46a : ∀ r s, 0 ≤ r → r < s → s ≤ rm → ϕ r - ϕ s ≤ m0 * (s - r))
    (h46b : ∀ r s, p1 ≤ r → r < s → s ≤ 1 → ϕ r - ϕ s ≤ M * (s - r))
    (h25 : ∀ p ∈ Set.Ico p1 1, Eq25 lam ϕ p)
    (h47a : ∀ p ∈ Set.Ico p1 1, m0 * (p * (1 - p)) ≤ J ϕ p)
    (h47b : ∀ p ∈ Set.Ico p1 1, J ϕ p ≤ p * (1 - p))
    (h47c : ∀ p ∈ Set.Ico p1 1, (M - 1) * J ϕ p ≤ p * (1 - (M + 1) * (1 - p))) :
    ∀ p ∈ Set.Ico p1 1,
      Eq37 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p ∧
        Eq38 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p := by
  intro p hp
  let B := p/J ϕ p
  let t := B*(1-p)
  let C := fun x => max (lam-x-t*ϕ x) 0
  have hpL := hp1lam.trans_le hp.1
  have hp0 := hϕ.lam_mem.1.trans hpL
  have hF := sub_pos.mpr hp.2
  have hJ : 0 < J ϕ p := lt_of_lt_of_le (mul_pos hm0 (mul_pos hp0 hF)) (h47a p hp)
  have hB : 0 < B := div_pos hp0 hJ
  have hBJ : B*J ϕ p=p := div_mul_cancel₀ _ hJ.ne'
  have htJ : t*J ϕ p=p*(1-p) := by dsimp [t]; rw [mul_right_comm,hBJ]
  have ht1 : 1 ≤ t := by apply le_of_mul_le_mul_right _ hJ; linarith [h47b p hp]
  have ht0 := zero_le_one.trans ht1
  have htm : t*m0 ≤ 1 := by
    apply le_of_mul_le_mul_right _ hJ
    nlinarith only [h47a p hp,congrArg (fun X => m0*X) htJ]
  have hprim := eq_43_44 hϕ
  have h48 (q : ℝ) (hq : q ∈ Icc 0 lam) : q+B*deltaP ϕ p q ≤ lam := by
    have hh := h25 p hp q hq.1 (le_min (hq.2.trans hpL.le) hq.2)
    change p * deltaP ϕ p q ≤ (lam - q) * J ϕ p at hh
    have he : B*deltaP ϕ p q * J ϕ p = p*deltaP ϕ p q := by rw [mul_right_comm,hBJ]
    apply le_of_mul_le_mul_right _ hJ; nlinarith only [he,hh]
  have hΔ (q : ℝ) (hq : q ∈ Icc 0 p) : B*deltaP ϕ p q ≤ t*ϕ q := by
    have hi := mul_le_mul_of_nonneg_left (hprim.1 p q hq.1 hq.2 hp.2.le).2.1 hB.le
    simpa only [t,mul_assoc] using hi
  have hc0 (x : ℝ) : 0 ≤ C x := le_max_right _ _
  have hzero := (gPhi_properties hϕ).1
  constructor
  · intro x hx
    constructor
    · intro q hq hqm
      have hqp := hqm.trans (min_le_left _ _)
      have hqx := hqm.trans (min_le_right _ _)
      have hl := h48 q ⟨hq,hqx.trans hx.2.le⟩
      change q+B*deltaP ϕ p q+C x ≤ lam
      by_cases hr : rm ≤ x
      · have hxline := hline x ⟨hr,by linarith [hx.2,hzp]⟩
        have hc : C x=0 := by apply max_eq_right; nlinarith [mul_le_mul_of_nonneg_right ht1 (hϕ.pos x hx).le]
        rw [hc,add_zero];exact hl
      · have hlip : ϕ q-ϕ x ≤ m0*(x-q) := by
          rcases hqx.lt_or_eq with lo | eq
          · exact h46a q x hq lo (le_of_not_ge hr)
          · rw [eq];simp
        dsimp only [C];rw [add_max];apply max_le
        · have ha := mul_le_mul_of_nonneg_left hlip ht0
          have hb := mul_le_mul_of_nonneg_right htm (sub_nonneg.mpr hqx)
          nlinarith only [hΔ q ⟨hq,hqp⟩,ha,hb]
        · simpa using hl
    · intro _ _ _ hpx; linarith [hx.2]
  · intro x hx
    have hφ := hϕ.pos x hx
    let R := (lam-x)/ϕ x
    have hR : 1 ≤ R := (one_le_div hφ).mpr (hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hϕ.lam_mem.2.le⟩)
    have hcancel : ϕ x*R=lam-x := by dsimp [R];field_simp
    have hfix : ϕ (lam+(1-p)) = -(1-p) := by
      rw [hline]; ring
      exact ⟨by linarith,by linarith [hp.1]⟩
    have htail {q z : ℝ} (hq : q ∈ Icc 0 lam) (hz : z ∈ Icc p 1) :=
      large_tail hϕ hpL hp.2 hq hz hM hJ (h25 p hp) hfix (fun r s hr => h46b r s (hp.1.trans hr)) (h47c p hp)
    constructor
    · intro q hq hqp
      change ϕ x*(q+B*deltaP ϕ p q+Wx lam ϕ x q-lam) ≤ max (-ϕ q) 0*C x
      by_cases hqL : q ≤ lam
      · rw [show Wx lam ϕ x q=0 from if_pos hqL,add_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le (sub_nonpos.mpr (h48 _ ⟨hq,hqL⟩))).trans
          (mul_nonneg (le_max_right _ _) (hc0 x))
      · have hqφ := (gPhi_properties hϕ).2.1 q ⟨le_of_not_ge hqL,hqp.trans hp.2.le⟩
        rw [Wx,if_neg hqL,max_eq_left (neg_nonneg.mpr hqφ)]
        have hh := mul_le_mul_of_nonneg_left (hΔ q ⟨hq,hqp⟩) hφ.le
        have hv : lam-x-t*ϕ x ≤ C x := le_max_left _ _
        have hneg := mul_le_mul_of_nonpos_right hv hqφ
        nlinarith only [hh,hneg,congrArg (fun r => r*ϕ q) hcancel]
    · intro q z hq hqp hpz hz
      have hzL := hpL.trans_le hpz
      have hzφ := (gPhi_properties hϕ).2.1 z ⟨hzL.le,hz⟩
      change ϕ x*(q+B*KP ϕ p q z+Wx lam ϕ x q-Wx lam ϕ x z) ≤ max (-ϕ z) 0*C x
      rw [show Wx lam ϕ x z=lam-z-R*ϕ z from if_neg (not_le.mpr hzL),max_eq_left (neg_nonneg.mpr hzφ)]
      have hn := mul_nonneg (neg_nonneg.mpr hzφ) (hc0 x)
      by_cases hqL : q ≤ lam
      · have hh := htail (q := q) ⟨hq,hqL⟩ ⟨hpz,hz⟩
        have hv := mul_le_mul_of_nonpos_right hR hzφ
        have hi : q+B*KP ϕ p q z-(lam-z-R*ϕ z) ≤ 0 := by linarith
        rw [show Wx lam ϕ x q=0 from if_pos hqL,add_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le hi).trans hn
      · have hh := large_high_tail hϕ hconc hadd ⟨hpL,hp.2⟩ ⟨le_of_not_ge hqL,hqp⟩
          ⟨hpz,hz⟩ hB.le hBJ hR (htail (q := lam) ⟨hϕ.lam_mem.1.le,le_rfl⟩ ⟨hpz,hz⟩) hzero
        rw [show Wx lam ϕ x q=lam-q-R*ϕ q from if_neg hqL]
        exact (mul_nonpos_of_nonneg_of_nonpos hφ.le (by linarith)).trans hn

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set MeasureTheory

private theorem integral_affine (a b : ℝ) (h : ℝ) :
    (∫ u in (0:ℝ)..h,a+b*u)=a*h+b*h^2/2 := by
  rw [intervalIntegral.integral_add (f:=fun _ : ℝ => a) (g:=fun u : ℝ => b*u) intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable 0 h),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [sub_zero,smul_eq_mul,zero_pow (by decide : 2 ≠ 0)]
  ring


theorem tail_primitive_bounds {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (tail : ∀ x ∈ Icc (99/100:ℝ) 1,2*(1-x) ≤ ϕ x+1 ∧ ϕ x+1 ≤ 63/10*(1-x))
    (p : ℝ) (hp : p ∈ Icc (99/100:ℝ) 1) :
    let h := 1-p
    h-(63/20)*h^2 ≤ J ϕ p ∧ J ϕ p ≤ p*h := by
  let h := 1-p
  have hh : 0 ≤ h := sub_nonneg.mpr hp.2
  have ph : p+h=1 := by dsimp [h];ring
  have hJ := J_increment hϕ (a:=p) (s:=h) (by linarith [hp.1]) hh ph.le
  rw [ph,show J ϕ 1=0 from hϕ.integral_eq_zero,zero_sub] at hJ
  have hI : IntervalIntegrable (fun u : ℝ => ϕ (p+u)) volume 0 h := by
    apply ContinuousOn.intervalIntegrable_of_Icc hh
    apply hϕ.continuousOn.comp (f:=fun u : ℝ => p+u) (by fun_prop)
    intro u hu;exact ⟨by linarith [hu.1,hp.1],by linarith [hu.2]⟩
  have hb (u : ℝ) (hu : u ∈ Icc 0 h) := tail (p+u) (show p+u ∈ Icc (99/100:ℝ) 1 from
    ⟨by linarith [hp.1,hu.1],by linarith [hu.2]⟩)
  have hlo := intervalIntegral.integral_mono_on hh
    (f:=fun u : ℝ => (-1+2*h)+(-2)*u) (g:=fun u : ℝ => ϕ (p+u))
    ((show Continuous (fun u : ℝ => (-1+2*h)+(-2)*u) by fun_prop).intervalIntegrable 0 h) hI
    (fun u hu => by linarith [(hb u hu).1])
  have hhi := intervalIntegral.integral_mono_on hh
    (f:=fun u : ℝ => ϕ (p+u)) (g:=fun u : ℝ => (-1+(63/10)*h)+(-63/10)*u) hI
    ((show Continuous (fun u : ℝ => (-1+(63/10)*h)+(-63/10)*u) by fun_prop).intervalIntegrable 0 h)
    (fun u hu => by linarith [(hb u hu).2])
  rw [← hJ,integral_affine] at hlo hhi
  change h-63/20*h^2 ≤ J ϕ p ∧ J ϕ p ≤ p*h
  constructor
  · nlinarith only [hhi]
  · have hprod : p*h=(1-h)*h := by dsimp [h];ring
    rw [hprod];nlinarith only [hlo]


theorem eq25_on_cell {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {p q s : ℝ} (hp : p ∈ Icc (99/100:ℝ) 1) (hq : q ∈ Icc 0 (min p lam))
    (hJ : 1-p-63/20*(1-p)^2 ≤ J ϕ p)
    (hs : ∀ x ∈ Icc q (q+(1-p)),s ≤ sigma lam ϕ x)
    (hcell : (1-p)*(43/20*(lam-q)-p/2) ≤ p*s) :
    p*(J ϕ (1-p+q)-J ϕ q) ≤ (lam-q)*J ϕ p := by
  let h := 1-p
  have hh : 0 ≤ h := sub_nonneg.mpr hp.2
  have ph : p+h=1 := by dsimp [h];ring
  have qh1 : q+h ≤ 1 := by linarith [hq.2.trans (min_le_left _ _)]
  have hI : IntervalIntegrable (fun u : ℝ => ϕ (q+u)) volume 0 h := by
    apply ContinuousOn.intervalIntegrable_of_Icc hh
    apply hϕ.continuousOn.comp (f:=fun u : ℝ => q+u) (by fun_prop)
    intro u hu;exact ⟨by linarith [hu.1,hq.1],by linarith [hu.2]⟩
  have hbd := intervalIntegral.integral_mono_on hh
    (f:=fun u : ℝ => ϕ (q+u)) (g:=fun u : ℝ => (lam-q-s)+(-1)*u) hI
    ((show Continuous (fun u : ℝ => (lam-q-s)+(-1)*u) by fun_prop).intervalIntegrable 0 h)
    (fun u hu => by
      have hv := hs (q+u) ⟨by linarith [hu.1],by change q+u ≤ q+h;linarith [hu.2]⟩
      unfold sigma at hv;linarith)
  rw [← J_increment hϕ hq.1 hh qh1,integral_affine] at hbd
  rw [show 1-p+q=q+h by dsimp [h];ring]
  have hqL := sub_nonneg.mpr (hq.2.trans (min_le_right _ _))
  have hp0 : 0 ≤ p := by linarith [hp.1]
  change h-63/20*h^2 ≤ J ϕ p at hJ
  change h*(43/20*(lam-q)-p/2) ≤ p*s at hcell
  have he : p*h-(h-63/20*h^2)=(43/20)*h^2 := by dsimp [h];ring
  have he' := congrArg (fun x => (lam-q)*x) he
  nlinarith only [mul_le_mul_of_nonneg_left hbd hp0,mul_le_mul_of_nonneg_left hJ hqL,
    mul_le_mul_of_nonneg_left hcell hh,he']


theorem json_eq25 {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction (703/1250) ϕ)
    (hσ : AntitoneOn (sigma (703/1250) ϕ) (Icc 0 (783/1000)))
    (slack₁ : 8/100 ≤ sigma (703/1250) ϕ (11/100))
    (slack₂ : 4/100 ≤ sigma (703/1250) ϕ (13/50))
    (slack₃ : 3/1000 ≤ sigma (703/1250) ϕ (41/125))
    (slack₄ : 4/10000 ≤ sigma (703/1250) ϕ (69/200))
    (tail : ∀ x ∈ Icc (99/100:ℝ) 1,2*(1-x) ≤ ϕ x+1 ∧ ϕ x+1 ≤ 63/10*(1-x)) :
    ∀ p ∈ Ico (99/100:ℝ) 1,Eq25 (703/1250) ϕ p := by
  intro p hp q hq hqp
  have hp' := (show p ∈ Icc (99/100:ℝ) 1 from ⟨hp.1,hp.2.le⟩)
  have hb := (tail_primitive_bounds hϕ tail p hp').1
  have h₀ : 0 ≤ 1-p := by linarith [hp.2]
  have h₁ : 1-p ≤ 1/100 := by linarith [hp.1]
  have qL := hqp.trans (min_le_right _ _)
  have bound (R s : ℝ) (hR : R ≤ 783/1000) (hqr : q+(1-p) ≤ R)
      (hs : s ≤ sigma (703/1250) ϕ R) : ∀ x ∈ Icc q (q+(1-p)),s ≤ sigma (703/1250) ϕ x := by
    intro x hx
    exact hs.trans (hσ ⟨hq.trans hx.1,(hx.2.trans hqr).trans hR⟩ ⟨hq.trans (by linarith),hR⟩ (hx.2.trans hqr))
  have scalar (L s : ℝ) (hl : L ≤ q) (hs : 0 ≤ s)
      (hn : (1/100)*max (43/20*(703/1250-L)-(99/100)/2) 0 ≤ 99/100*s) :
      (1-p)*(43/20*(703/1250-q)-p/2) ≤ p*s := by
    have hl' : 43/20*(703/1250-q)-p/2 ≤ max (43/20*(703/1250-L)-(99/100)/2) 0 :=
      (by linarith [hp.1] : _ ≤ 43/20*(703/1250-L)-(99/100)/2).trans (le_max_left _ _)
    exact (mul_le_mul_of_nonneg_left hl' h₀).trans
      ((mul_le_mul_of_nonneg_right h₁ (le_max_right _ _)).trans (hn.trans (mul_le_mul_of_nonneg_right hp.1 hs)))
  by_cases q₁ : q≤1/10
  · exact eq25_on_cell hϕ hp' ⟨hq,hqp⟩ hb (bound _ _ (by norm_num) (by linarith) slack₁)
      (scalar 0 _ hq (by norm_num) (by norm_num))
  by_cases q₂ : q≤1/4
  · exact eq25_on_cell hϕ hp' ⟨hq,hqp⟩ hb (bound _ _ (by norm_num) (by linarith) slack₂)
      (scalar (1/10) _ (by linarith) (by norm_num) (by norm_num))
  by_cases q₃ : q≤159/500
  · exact eq25_on_cell hϕ hp' ⟨hq,hqp⟩ hb (bound _ _ (by norm_num) (by linarith) slack₃)
      (scalar (1/4) _ (by linarith) (by norm_num) (by norm_num))
  by_cases q₄ : q≤67/200
  · exact eq25_on_cell hϕ hp' ⟨hq,hqp⟩ hb (bound _ _ (by norm_num) (by linarith) slack₄)
      (scalar (159/500) _ (by linarith) (by norm_num) (by norm_num))
  apply eq25_on_cell hϕ hp' ⟨hq,hqp⟩ hb (s:=0)
  · intro x hx;apply sub_nonneg.mpr (hϕ.le_lam_sub _ ⟨hq.trans hx.1,by linarith [hx.2]⟩)
  · exact scalar (67/200) _ (by linarith) (by norm_num) (by norm_num)

end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set


structure EndpointData (ϕ : ℝ → ℝ) : Prop where
  score : IsScoreFunction (703/1250) ϕ
  decreasing : AntitoneOn (fun x => ϕ x+x) (Icc (703/1250) 1)
  concave : ConcaveOn ℝ (Icc (703/1250) 1) ϕ
  line : ∀ r ∈ Icc (4356751/12500000:ℝ) (783/1000),ϕ r=703/1250-r
  initialSlope : ∀ r s,0 ≤ r → r<s → s ≤ 4356751/12500000 → ϕ r-ϕ s ≤ (93/100)*(s-r)
  finalSlope : ∀ r s,99/100 ≤ r → r<s → s ≤ 1 → 2*(s-r) ≤ ϕ r-ϕ s ∧ ϕ r-ϕ s ≤ (63/10)*(s-r)
  origin : ϕ 0 ≤ 44/100
  atLowCut : 43/100 ≤ ϕ (1/100)
  firstKnot : ϕ (527/2000) ≤ 26/100
  gapOne : 8/100 ≤ sigma (703/1250) ϕ (11/100)
  gapTwo : 4/100 ≤ sigma (703/1250) ϕ (13/50)
  gapThree : 3/1000 ≤ sigma (703/1250) ϕ (41/125)
  gapFour : 4/10000 ≤ sigma (703/1250) ϕ (69/200)

theorem sigma_antitone {ϕ : ℝ → ℝ} (e : EndpointData ϕ) : AntitoneOn (sigma (703/1250) ϕ) (Icc 0 (783/1000)) := by
  intro r hr s hs hrs
  have pre (x y : ℝ) (h0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 4356751/12500000) :
      sigma (703/1250) ϕ y ≤ sigma (703/1250) ϕ x := by
    rcases hxy.eq_or_lt with rfl|h
    · rfl
    · unfold sigma;linarith [e.initialSlope x y h0 h hy]
  by_cases h : s ≤ 4356751/12500000
  · exact pre r s hr.1 hrs h
  have hz : sigma (703/1250) ϕ s=0 := by unfold sigma;rw [e.line s ⟨le_of_not_ge h,hs.2⟩];ring
  rw [hz];exact sub_nonneg.mpr (e.score.le_lam_sub _ ⟨hr.1,by linarith [hr.2]⟩)

private theorem tail_anchor {ϕ : ℝ → ℝ} (e : EndpointData ϕ) (x : ℝ) (hx : x ∈ Icc (99/100:ℝ) 1) :
    2*(1-x) ≤ ϕ x+1 ∧ ϕ x+1 ≤ 63/10*(1-x) := by
  rcases hx.2.lt_or_eq with h|rfl
  · simpa [e.score.at_one] using e.finalSlope x 1 hx.1 h le_rfl
  · norm_num [e.score.at_one]


theorem high_extension {ϕ : ℝ → ℝ} (e : EndpointData ϕ) : ∀ p ∈ Ico (99/100:ℝ) 1,
    Eq37 (703/1250) ϕ (fun p => p/J ϕ p) (fun p x => max (703/1250-x-p/J ϕ p*(1-p)*ϕ x) 0) p ∧
    Eq38 (703/1250) ϕ (fun p => p/J ϕ p) (fun p x => max (703/1250-x-p/J ϕ p*(1-p)*ϕ x) 0) p := by
  apply lemma_14_ii e.score e.decreasing (by norm_num) (by norm_num) (rm:=4356751/12500000) (zp:=783/1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) e.line e.concave (m0:=93/100) (M:=63/10)
    (by norm_num) (by norm_num) (by norm_num) e.initialSlope (fun r s hr hrs hs => (e.finalSlope r s hr hrs hs).2)
  · exact json_eq25 e.score (sigma_antitone e) e.gapOne e.gapTwo e.gapThree e.gapFour (tail_anchor e)
  · intro p hp
    have h := (tail_primitive_bounds e.score (tail_anchor e) p ⟨hp.1,hp.2.le⟩).1
    nlinarith only [h,mul_nonneg (show 0≤1-p by linarith [hp.2]) (show 0≤7/100-(222/100)*(1-p) by linarith [hp.1])]
  · intro p hp;exact (tail_primitive_bounds e.score (tail_anchor e) p ⟨hp.1,hp.2.le⟩).2
  · intro p hp
    have h := (tail_primitive_bounds e.score (tail_anchor e) p ⟨hp.1,hp.2.le⟩).2
    have a : 0<p := by linarith [hp.1]
    nlinarith only [h,mul_nonneg a.le (show 0 ≤ 1-(126/10)*(1-p) by linarith [hp.1])]

end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set PaperCurve


theorem chain_slope_lower {ps : List Piece} {a b : Knot} (chain : Chain a ps b)
    {f : ℝ → ℝ} (values : ∀ row ∈ ps,∀ x ∈ Icc (row.lo:ℝ) row.hi,f x=row.value x)
    {x y v : ℝ} (hx : (a.x:ℝ) ≤ x) (hy : y ≤ (b.x:ℝ)) (hxy : x ≤ y)
    (bound : ∀ row ∈ ps,∀ t ∈ Ioo (row.lo:ℝ) row.hi, x<t → t<y → v ≤ row.slope t) :
    v*(y-x) ≤ f y-f x := by
  induction ps generalizing a x y with
  | nil =>
    have ha : a=b := chain
    have he : x=y := by rw [ha] at hx;linarith
    simp [he]
  | cons row ps ih =>
    rcases chain with ⟨rfl,hh,chain⟩
    change (row.lo:ℝ) ≤ x at hx
    have hw : (row.lo:ℝ)<row.hi := by exact_mod_cast hh
    have one {s t : ℝ} (hs : row.lo ≤ s) (hst : s ≤ t) (ht : t ≤ row.hi) (hxs : x ≤ s) (hty : t ≤ y) :
        v*(t-s) ≤ f t-f s := by
      rw [values row (by simp) t ⟨hs.trans hst,ht⟩,values row (by simp) s ⟨hs,hst.trans ht⟩]
      apply (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv row.continuous_value.continuousOn
        (fun z _ => (row.hasDeriv_value z).differentiableAt.differentiableWithinAt) _ s ⟨le_rfl,hst⟩ t ⟨hst,le_rfl⟩ hst
      intro z hz
      rw [interior_Icc] at hz
      rw [(row.hasDeriv_value z).deriv]
      exact bound row (by simp) z ⟨hs.trans_lt hz.1,hz.2.trans_le ht⟩ (hxs.trans_lt hz.1) (hz.2.trans_le hty)
    by_cases h : y ≤ row.hi
    · exact one hx hxy h le_rfl le_rfl
    have tail (s : ℝ) (hs : row.hi ≤ s) (hxs : x ≤ s) (hsy : s ≤ y) : v*(y-s) ≤ f y-f s := by
      apply ih chain (fun r hr => values r (by simp [hr])) hs hy hsy
      intro r hr t ht hst hty
      exact bound r (by simp [hr]) t ht (hxs.trans_lt hst) hty
    by_cases hx' : row.hi ≤ x
    · exact tail x hx' le_rfl hxy
    have left := one hx (le_of_not_ge hx') le_rfl le_rfl (le_of_not_ge h)
    have right := tail row.hi le_rfl (le_of_not_ge hx') (le_of_not_ge h)
    linarith only [left,right]


theorem chain_slope_upper {ps : List Piece} {a b : Knot} (chain : Chain a ps b)
    {f : ℝ → ℝ} (values : ∀ row ∈ ps,∀ x ∈ Icc (row.lo:ℝ) row.hi,f x=row.value x)
    {x y v : ℝ} (hx : (a.x:ℝ) ≤ x) (hy : y ≤ (b.x:ℝ)) (hxy : x ≤ y)
    (bound : ∀ row ∈ ps,∀ t ∈ Ioo (row.lo:ℝ) row.hi, x<t → t<y → row.slope t ≤ v) :
    f y-f x ≤ v*(y-x) := by
  induction ps generalizing a x y with
  | nil =>
    have ha : a=b := chain
    have he : x=y := by rw [ha] at hx;linarith
    simp [he]
  | cons row ps ih =>
    rcases chain with ⟨rfl,hh,chain⟩
    change (row.lo:ℝ) ≤ x at hx
    have one {s t : ℝ} (hs : row.lo ≤ s) (hst : s ≤ t) (ht : t ≤ row.hi) (hxs : x ≤ s) (hty : t ≤ y) :
        f t-f s ≤ v*(t-s) := by
      rw [values row (by simp) t ⟨hs.trans hst,ht⟩,values row (by simp) s ⟨hs,hst.trans ht⟩]
      apply (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le row.continuous_value.continuousOn
        (fun z _ => (row.hasDeriv_value z).differentiableAt.differentiableWithinAt) _ s ⟨le_rfl,hst⟩ t ⟨hst,le_rfl⟩ hst
      intro z hz
      rw [interior_Icc] at hz
      rw [(row.hasDeriv_value z).deriv]
      exact bound row (by simp) z ⟨hs.trans_lt hz.1,hz.2.trans_le ht⟩ (hxs.trans_lt hz.1) (hz.2.trans_le hty)
    by_cases h : y ≤ row.hi
    · exact one hx hxy h le_rfl le_rfl
    have tail (s : ℝ) (hs : row.hi ≤ s) (hxs : x ≤ s) (hsy : s ≤ y) : f y-f s ≤ v*(y-s) := by
      apply ih chain (fun r hr => values r (by simp [hr])) hs hy hsy
      intro r hr t ht hst hty
      exact bound r (by simp [hr]) t ht (hxs.trans_lt hst) hty
    by_cases hx' : row.hi ≤ x
    · exact tail x hx' le_rfl hxy
    have left := one hx (le_of_not_ge hx') le_rfl le_rfl (le_of_not_ge h)
    have right := tail row.hi le_rfl (le_of_not_ge hx') (le_of_not_ge h)
    linarith only [left,right]

theorem exists_covering_piece {ps : List Piece} {a b : Knot} (chain : Chain a ps b)
    {x : ℝ} (hx : (a.x:ℝ) ≤ x) (hy : x<(b.x:ℝ)) : ∃ r∈ps,x∈Icc (r.lo:ℝ) r.hi := by
  induction ps generalizing a with
  | nil => rw [show a=b from chain] at hx;exact (hy.not_ge hx).elim
  | cons p ps ih =>
    rcases chain with ⟨rfl,_,chain⟩
    by_cases hh : x ≤ p.hi
    · exact ⟨p,by simp,⟨hx,hh⟩⟩
    · obtain ⟨r,hr,hw⟩ := ih chain (le_of_not_ge hh)
      exact ⟨r,by simp [hr],hw⟩


theorem chain_concave {ps : List Piece} {a b : Knot} (chain : Chain a ps b)
    {f : ℝ → ℝ} (values : ∀ row ∈ ps,∀ x ∈ Icc (row.lo:ℝ) row.hi,f x=row.value x)
    {l u : ℝ} (hl : (a.x:ℝ) ≤ l) (hu : u ≤ (b.x:ℝ))
    (decreasing : ∀ r∈ps,∀ s∈ps,∀ t∈Icc (r.lo:ℝ) r.hi,∀ z∈Icc (s.lo:ℝ) s.hi,
      l<t → t<z → z ≤ u → s.slope z ≤ r.slope t) : ConcaveOn ℝ (Icc l u) f := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc _ _)
  intro x y z hx hz hxy hyz
  obtain ⟨r,hr,hy⟩ := exists_covering_piece chain ((hl.trans hx.1).trans hxy.le) ((hyz.trans_le hz.2).trans_le hu)
  have hleft := chain_slope_lower chain values (hl.trans hx.1) ((hyz.le.trans hz.2).trans hu) hxy.le
    (v:=r.slope y) (fun row hrow t ht hxt hty => decreasing row hrow r hr t ⟨ht.1.le,ht.2.le⟩ y hy
      (hx.1.trans_lt hxt) hty (hyz.le.trans hz.2))
  have hright := chain_slope_upper chain values ((hl.trans hx.1).trans hxy.le) (hz.2.trans hu) hyz.le
    (v:=r.slope y) (fun row hrow t ht hyt htz => decreasing r hr row hrow y hy t ⟨ht.1.le,ht.2.le⟩
      (hx.1.trans_lt hxy) hyt (htz.le.trans hz.2))
  exact ((div_le_iff₀ (sub_pos.mpr hyz)).mpr hright).trans ((le_div_iff₀ (sub_pos.mpr hxy)).mpr hleft)

end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set PaperCurve
noncomputable section


def startSlope (r : Piece) : ℚ := r.c 1
def endSlope (r : Piece) : ℚ := r.c 1+2*r.c 2*(r.hi-r.lo)
def tailRow (r : Piece) : Prop := r.c 3=0 ∧ r.c 4=0 ∧ r.c 5=0 ∧ r.c 6=0 ∧ r.c 2 ≤ 0
instance (r : Piece) : Decidable (tailRow r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))


def descendingFrom (start : ℚ) : List Piece → Prop
  | [] => True
  | r::rs => startSlope r ≤ start ∧ tailRow r ∧ descendingFrom (endSlope r) rs
instance descendingFrom_decidable (start : ℚ) (ps : List Piece) : Decidable (descendingFrom start ps) := by
  induction ps generalizing start with
  | nil => exact isTrue trivial
  | cons r rs ih => letI := ih (endSlope r);exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem row_slope {r : Piece} (ht : tailRow r) (x : ℝ) :
    r.slope x=(r.c 1:ℝ)+2*(r.c 2:ℝ)*(x-r.lo) := by
  obtain ⟨a,b,c,d,_⟩ := ht
  simp [Piece.slope,Piece.slopeCoeffs,horner,a,b,c,d];ring

private theorem row_antitone {r : Piece} (ht : tailRow r) : Antitone r.slope := by
  intro x y hxy
  rw [row_slope ht,row_slope ht]
  have hc : (r.c 2:ℝ) ≤ 0 := by exact_mod_cast ht.2.2.2.2
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hc]

private theorem row_start {r : Piece} (h : tailRow r) : r.slope r.lo=(startSlope r:ℝ) := by
  rw [row_slope h];simp [startSlope]
private theorem row_end {r : Piece} (h : tailRow r) : r.slope r.hi=(endSlope r:ℝ) := by
  rw [row_slope h];push_cast [endSlope];ring

private theorem row_after {ps : List Piece} {a b : Knot} (hc : Chain a ps b) {r : Piece} (hr : r∈ps) : a.x ≤ r.lo := by
  induction ps generalizing a with
  | nil => cases hr
  | cons p ps ih =>
    obtain ⟨rfl,hh,ch⟩ := hc
    obtain he|he := List.mem_cons.mp hr
    · subst r;exact le_rfl
    · exact hh.le.trans (ih ch he)

private theorem all_below {ps : List Piece} {a b : Knot} (hc : Chain a ps b) {k : ℚ}
    (hd : descendingFrom k ps) {r : Piece} (hr : r∈ps) {x : ℝ} (hx : x ∈ Icc (r.lo:ℝ) r.hi) :
    r.slope x ≤ (k:ℝ) := by
  induction ps generalizing a k with
  | nil => cases hr
  | cons p ps ih =>
    obtain ⟨_,hw,ch⟩ := hc
    obtain ⟨h₀,hp,h₁⟩ := hd
    have hstart : p.slope p.lo ≤ k := by rw [row_start hp];exact_mod_cast h₀
    obtain he|he := List.mem_cons.mp hr
    · subst r;exact ((row_antitone hp) hx.1).trans hstart
    · have ht := ih ch h₁ he
      have hw' : (p.lo:ℝ) ≤ p.hi := by exact_mod_cast hw.le
      exact ht.trans (by rw [← row_end hp];exact ((row_antitone hp) hw').trans hstart)


theorem descending_slopes {ps : List Piece} {a b : Knot} (hc : Chain a ps b) {k : ℚ}
    (hd : descendingFrom k ps) {r s : Piece} (hr : r∈ps) (hs : s∈ps) {x y : ℝ}
    (hx : x ∈ Icc (r.lo:ℝ) r.hi) (hy : y ∈ Icc (s.lo:ℝ) s.hi) (hxy : x<y) : s.slope y ≤ r.slope x := by
  induction ps generalizing a k with
  | nil => cases hr
  | cons p ps ih =>
    obtain ⟨_,hw,ch⟩ := hc
    obtain ⟨h₀,hp,h₁⟩ := hd
    rcases List.mem_cons.mp hr with hr|hr <;> rcases List.mem_cons.mp hs with hs|hs
    · subst r;subst s;exact row_antitone hp hxy.le
    · subst r;have ht := all_below ch h₁ hs hy
      rw [← row_end hp] at ht
      exact ht.trans (row_antitone hp hx.2)
    · subst s;have hl := row_after ch hr
      have hl' : (p.hi:ℝ) ≤ r.lo := by exact_mod_cast hl
      exact (hxy.not_ge ((hy.2.trans hl').trans hx.1)).elim
    · exact ih ch h₁ hr hs


def slopeChain (start : ℚ) : List Piece → Prop
  | [] => True
  | p::ps => if p.hi ≤ lamQ then slopeChain start ps else descendingFrom start (p::ps)
instance slopeChain_decidable (k : ℚ) (ps : List Piece) : Decidable (slopeChain k ps) := by
  induction ps with
  | nil => exact isTrue trivial
  | cons r rs ih => unfold slopeChain;split <;> infer_instance

theorem post_slopes {ps : List Piece} {a b : Knot} (hc : Chain a ps b) {k : ℚ}
    (hd : slopeChain k ps) {r s : Piece} (hr : r∈ps) (hs : s∈ps) {x y : ℝ}
    (hx : x ∈ Icc (r.lo:ℝ) r.hi) (hy : y ∈ Icc (s.lo:ℝ) s.hi) (hl : lam<x) (hxy : x<y) : s.slope y ≤ r.slope x := by
  induction ps generalizing a with
  | nil => cases hr
  | cons p ps ih =>
    unfold slopeChain at hd
    split at hd
    · rename_i h
      rcases hc with ⟨_,_,ch⟩
      have he : (p.hi:ℝ) ≤ lam := by unfold lam;exact_mod_cast h
      rcases List.mem_cons.mp hr with hr|hr
      · subst r;exact (hl.not_ge (hx.2.trans he)).elim
      rcases List.mem_cons.mp hs with hs|hs
      · subst s;exact ((hl.trans hxy).not_ge (hy.2.trans he)).elim
      · exact ih ch hd hr hs
    · exact descending_slopes hc hd hr hs hx hy hxy

end
end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open PaperCurve
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 100000000


def slopeTests (p : Piece) : Prop :=
  (p.lo<rcQ → 0 ≤ p.slopeTest (93/100) 1) ∧
  (99/100<p.hi → 0 ≤ p.slopeTest (63/10) 1 ∧ 0 ≤ p.slopeTest (-2) (-1))
instance (p : Piece) : Decidable (slopeTests p) := inferInstanceAs (Decidable (_ ∧ _))

theorem data_descending : slopeChain 0 pieces := by decide +kernel

def qsample (x : ℚ) : List Piece → ℚ
  | [] => endKnot.y
  | p::ps => if x ≤ p.hi then p.qvalue x else qsample x ps

private theorem cast_qsample (x : ℚ) (ps : List Piece) :
    (qsample x ps:ℝ)=scoreEval endKnot ps x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hx : x ≤ p.hi
    · simpa [qsample,scoreEval,select,hx,show (x:ℝ) ≤ p.hi by exact_mod_cast hx] using p.cast_qvalue x
    · simp [qsample,scoreEval,select,hx,show ¬(x:ℝ) ≤ p.hi by exact_mod_cast hx,ih,scoreEval]  

theorem score_rational (x : ℚ) : score (x:ℝ)=(qsample x pieces:ℝ) := (cast_qsample x _).symm

theorem score_samples : score 0 ≤ 44/100 ∧ 43/100 ≤ score (1/100) ∧ score (527/2000) ≤ 26/100 ∧
    8/100 ≤ sigma (703/1250) score (11/100) ∧ 4/100 ≤ sigma (703/1250) score (13/50) ∧
    3/1000 ≤ sigma (703/1250) score (41/125) ∧ 4/10000 ≤ sigma (703/1250) score (69/200) := by
  have hu (x v : ℚ) (h : qsample x pieces ≤ v) : score (x:ℝ) ≤ (v:ℝ) := by rw [score_rational];exact_mod_cast h
  have hl (x v : ℚ) (h : v ≤ qsample x pieces) : (v:ℝ) ≤ score (x:ℝ) := by rw [score_rational];exact_mod_cast h
  have hg (x v : ℚ) (h : v ≤ lamQ-x-qsample x pieces) : (v:ℝ) ≤ sigma (703/1250) score (x:ℝ) := by
    unfold sigma;rw [score_rational];have he : (lamQ:ℝ)=703/1250 := by norm_num [lamQ]
    rw [← he];exact_mod_cast h
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have h := hu 0 (44/100) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hl (1/100) (43/100) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hu (527/2000) (26/100) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hg (11/100) (8/100) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hg (13/50) (4/100) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hg (41/125) (3/1000) (by decide +kernel)
    norm_num at h ⊢;exact h
  · have h := hg (69/200) (4/10000) (by decide +kernel)
    norm_num at h ⊢;exact h

private theorem slopeCheck00 : rows00.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck01 : rows01.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck02 : rows02.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck03 : rows03.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck04 : rows04.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck05 : rows05.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck06 : rows06.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck07 : rows07.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck08 : rows08.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck09 : rows09.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck10 : rows10.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck11 : rows11.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck12 : rows12.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck13 : rows13.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck14 : rows14.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck15 : rows15.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck16 : rows16.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck17 : rows17.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck18 : rows18.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck19 : rows19.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck20 : rows20.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck21 : rows21.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck22 : rows22.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck23 : rows23.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck24 : rows24.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck25 : rows25.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck26 : rows26.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck27 : rows27.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck28 : rows28.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck29 : rows29.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck30 : rows30.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck31 : rows31.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck32 : rows32.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck33 : rows33.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck34 : rows34.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck35 : rows35.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck36 : rows36.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck37 : rows37.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck38 : rows38.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck39 : rows39.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck40 : rows40.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck41 : rows41.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck42 : rows42.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck43 : rows43.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck44 : rows44.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck45 : rows45.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck46 : rows46.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck47 : rows47.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck48 : rows48.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck49 : rows49.all (fun p => decide (slopeTests p))=true := by decide +kernel
private theorem slopeCheck50 : rows50.all (fun p => decide (slopeTests p))=true := by decide +kernel

private def allSlopes (ps : List Piece) : Prop := ∀ p∈ps,slopeTests p
private theorem slopes_of_all {ps : List Piece} (h : ps.all (fun p => decide (slopeTests p))=true) : allSlopes ps := by
  intro p hp
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp h p hp

private theorem slopes_join {ps qs : List Piece} (h : allSlopes ps) (k : allSlopes qs) : allSlopes (ps++qs) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact h p hp
  · exact k p hp

theorem data_slopeTests : ∀ p∈pieces,slopeTests p := by
  change allSlopes pieces
  unfold pieces
  have rowNil : allSlopes [] := by intro p hp;cases hp
  have row00 : allSlopes rows00 := slopes_of_all (ps:=rows00) slopeCheck00
  have row01 : allSlopes rows01 := slopes_of_all (ps:=rows01) slopeCheck01
  have row02 : allSlopes rows02 := slopes_of_all (ps:=rows02) slopeCheck02
  have row03 : allSlopes rows03 := slopes_of_all (ps:=rows03) slopeCheck03
  have row04 : allSlopes rows04 := slopes_of_all (ps:=rows04) slopeCheck04
  have row05 : allSlopes rows05 := slopes_of_all (ps:=rows05) slopeCheck05
  have row06 : allSlopes rows06 := slopes_of_all (ps:=rows06) slopeCheck06
  have row07 : allSlopes rows07 := slopes_of_all (ps:=rows07) slopeCheck07
  have row08 : allSlopes rows08 := slopes_of_all (ps:=rows08) slopeCheck08
  have row09 : allSlopes rows09 := slopes_of_all (ps:=rows09) slopeCheck09
  have row10 : allSlopes rows10 := slopes_of_all (ps:=rows10) slopeCheck10
  have row11 : allSlopes rows11 := slopes_of_all (ps:=rows11) slopeCheck11
  have row12 : allSlopes rows12 := slopes_of_all (ps:=rows12) slopeCheck12
  have row13 : allSlopes rows13 := slopes_of_all (ps:=rows13) slopeCheck13
  have row14 : allSlopes rows14 := slopes_of_all (ps:=rows14) slopeCheck14
  have row15 : allSlopes rows15 := slopes_of_all (ps:=rows15) slopeCheck15
  have row16 : allSlopes rows16 := slopes_of_all (ps:=rows16) slopeCheck16
  have row17 : allSlopes rows17 := slopes_of_all (ps:=rows17) slopeCheck17
  have row18 : allSlopes rows18 := slopes_of_all (ps:=rows18) slopeCheck18
  have row19 : allSlopes rows19 := slopes_of_all (ps:=rows19) slopeCheck19
  have row20 : allSlopes rows20 := slopes_of_all (ps:=rows20) slopeCheck20
  have row21 : allSlopes rows21 := slopes_of_all (ps:=rows21) slopeCheck21
  have row22 : allSlopes rows22 := slopes_of_all (ps:=rows22) slopeCheck22
  have row23 : allSlopes rows23 := slopes_of_all (ps:=rows23) slopeCheck23
  have row24 : allSlopes rows24 := slopes_of_all (ps:=rows24) slopeCheck24
  have row25 : allSlopes rows25 := slopes_of_all (ps:=rows25) slopeCheck25
  have row26 : allSlopes rows26 := slopes_of_all (ps:=rows26) slopeCheck26
  have row27 : allSlopes rows27 := slopes_of_all (ps:=rows27) slopeCheck27
  have row28 : allSlopes rows28 := slopes_of_all (ps:=rows28) slopeCheck28
  have row29 : allSlopes rows29 := slopes_of_all (ps:=rows29) slopeCheck29
  have row30 : allSlopes rows30 := slopes_of_all (ps:=rows30) slopeCheck30
  have row31 : allSlopes rows31 := slopes_of_all (ps:=rows31) slopeCheck31
  have row32 : allSlopes rows32 := slopes_of_all (ps:=rows32) slopeCheck32
  have row33 : allSlopes rows33 := slopes_of_all (ps:=rows33) slopeCheck33
  have row34 : allSlopes rows34 := slopes_of_all (ps:=rows34) slopeCheck34
  have row35 : allSlopes rows35 := slopes_of_all (ps:=rows35) slopeCheck35
  have row36 : allSlopes rows36 := slopes_of_all (ps:=rows36) slopeCheck36
  have row37 : allSlopes rows37 := slopes_of_all (ps:=rows37) slopeCheck37
  have row38 : allSlopes rows38 := slopes_of_all (ps:=rows38) slopeCheck38
  have row39 : allSlopes rows39 := slopes_of_all (ps:=rows39) slopeCheck39
  have row40 : allSlopes rows40 := slopes_of_all (ps:=rows40) slopeCheck40
  have row41 : allSlopes rows41 := slopes_of_all (ps:=rows41) slopeCheck41
  have row42 : allSlopes rows42 := slopes_of_all (ps:=rows42) slopeCheck42
  have row43 : allSlopes rows43 := slopes_of_all (ps:=rows43) slopeCheck43
  have row44 : allSlopes rows44 := slopes_of_all (ps:=rows44) slopeCheck44
  have row45 : allSlopes rows45 := slopes_of_all (ps:=rows45) slopeCheck45
  have row46 : allSlopes rows46 := slopes_of_all (ps:=rows46) slopeCheck46
  have row47 : allSlopes rows47 := slopes_of_all (ps:=rows47) slopeCheck47
  have row48 : allSlopes rows48 := slopes_of_all (ps:=rows48) slopeCheck48
  have row49 : allSlopes rows49 := slopes_of_all (ps:=rows49) slopeCheck49
  have row50 : allSlopes rows50 := slopes_of_all (ps:=rows50) slopeCheck50
  have step01 := slopes_join (ps:=rows00) (qs:=rows01) row00 row01
  have step02 := slopes_join (ps:=rows00 ++ rows01) (qs:=rows02) step01 row02
  have step03 := slopes_join (ps:=rows00 ++ rows01 ++ rows02) (qs:=rows03) step02 row03
  have step04 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03) (qs:=rows04) step03 row04
  have step05 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04) (qs:=rows05) step04 row05
  have step06 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05) (qs:=rows06) step05 row06
  have step07 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06) (qs:=rows07) step06 row07
  have step08 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07) (qs:=rows08) step07 row08
  have step09 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08) (qs:=rows09) step08 row09
  have step10 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09) (qs:=rows10) step09 row10
  have step11 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10) (qs:=rows11) step10 row11
  have step12 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11) (qs:=rows12) step11 row12
  have step13 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12) (qs:=rows13) step12 row13
  have step14 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13) (qs:=rows14) step13 row14
  have step15 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14) (qs:=rows15) step14 row15
  have step16 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15) (qs:=rows16) step15 row16
  have step17 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16) (qs:=rows17) step16 row17
  have step18 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17) (qs:=rows18) step17 row18
  have step19 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18) (qs:=rows19) step18 row19
  have step20 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19) (qs:=rows20) step19 row20
  have step21 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20) (qs:=rows21) step20 row21
  have step22 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21) (qs:=rows22) step21 row22
  have step23 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22) (qs:=rows23) step22 row23
  have step24 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23) (qs:=rows24) step23 row24
  have step25 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24) (qs:=rows25) step24 row25
  have step26 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25) (qs:=rows26) step25 row26
  have step27 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26) (qs:=rows27) step26 row27
  have step28 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27) (qs:=rows28) step27 row28
  have step29 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28) (qs:=rows29) step28 row29
  have step30 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29) (qs:=rows30) step29 row30
  have step31 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30) (qs:=rows31) step30 row31
  have step32 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31) (qs:=rows32) step31 row32
  have step33 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32) (qs:=rows33) step32 row33
  have step34 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33) (qs:=rows34) step33 row34
  have step35 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34) (qs:=rows35) step34 row35
  have step36 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35) (qs:=rows36) step35 row36
  have step37 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36) (qs:=rows37) step36 row37
  have step38 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37) (qs:=rows38) step37 row38
  have step39 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38) (qs:=rows39) step38 row39
  have step40 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39) (qs:=rows40) step39 row40
  have step41 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40) (qs:=rows41) step40 row41
  have step42 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41) (qs:=rows42) step41 row42
  have step43 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42) (qs:=rows43) step42 row43
  have step44 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43) (qs:=rows44) step43 row44
  have step45 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44) (qs:=rows45) step44 row45
  have step46 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45) (qs:=rows46) step45 row46
  have step47 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45 ++ rows46) (qs:=rows47) step46 row47
  have step48 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45 ++ rows46 ++ rows47) (qs:=rows48) step47 row48
  have step49 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45 ++ rows46 ++ rows47 ++ rows48) (qs:=rows49) step48 row49
  have step50 := slopes_join (ps:=rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45 ++ rows46 ++ rows47 ++ rows48 ++ rows49) (qs:=rows50) step49 row50
  exact slopes_join (qs:=[]) step50 rowNil

end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set PaperCurve

private theorem cast_lam : lam=(703/1250:ℝ) := by norm_num [lam,lamQ]
private theorem cast_rc : rc=(4356751/12500000:ℝ) := by norm_num [rc,rcQ]
private theorem cast_zdep : zdep=(783/1000:ℝ) := by norm_num [zdep,zdepQ]

private theorem values : ∀ r ∈ pieces,∀ x∈Icc (r.lo:ℝ) r.hi,score x=r.value x :=
  fun _ hr _ hx => score_on_piece hr hx

theorem score_concave : ConcaveOn ℝ (Icc (703/1250:ℝ) 1) score := by
  apply chain_concave data_chain values (by norm_num [startKnot]) (by norm_num [endKnot])
  intro r hr s hs x hx y hy hxl hxy hyu
  exact post_slopes data_chain data_descending hr hs hx hy (by simpa only [cast_lam] using hxl) hxy

theorem initial_slope : ∀ r s : ℝ,0 ≤ r → r<s → s ≤ 4356751/12500000 → score r-score s ≤ 93/100*(s-r) := by
  intro r s hr hrs hs
  have hh := chain_slope_lower data_chain values (show (startKnot.x:ℝ) ≤ r by simpa [startKnot] using hr)
    (show s ≤ (endKnot.x:ℝ) by norm_num [endKnot];linarith) hrs.le (v:=-(93/100)) (by
      intro row hrow x hx hrx hxs
      have ht : row.lo<rcQ := by
        have he : (row.lo:ℝ)<(rcQ:ℝ) := by change (row.lo:ℝ)<rc;rw [cast_rc];linarith [hx.1]
        exact_mod_cast he
      have h := (data_slopeTests row hrow).1 ht
      have h' : (0:ℝ) ≤ (row.slopeTest (93/100) 1:ℝ) := by exact_mod_cast h
      have h'' := row.slope_bound (93/100) 1 (show x∈Icc (row.lo:ℝ) row.hi from ⟨hx.1.le,hx.2.le⟩)
      norm_num at h'' <;> linarith)
  linarith

theorem final_slope : ∀ r s : ℝ,99/100 ≤ r → r<s → s ≤ 1 →
    2*(s-r) ≤ score r-score s ∧ score r-score s ≤ 63/10*(s-r) := by
  intro r s hr hrs hs
  have hx : (startKnot.x:ℝ) ≤ r := by norm_num [startKnot];linarith
  have hy : s ≤ (endKnot.x:ℝ) := by simpa [endKnot] using hs
  have data (row : Piece) (hrow : row∈pieces) (x : ℝ) (hw : x∈Ioo (row.lo:ℝ) row.hi) (hrx : r<x) :
      -(63/10) ≤ row.slope x ∧ row.slope x ≤ -2 := by
    have hh : (99/100:ℚ)<row.hi := by
      have h : ((99/100:ℚ):ℝ)<row.hi := by push_cast;exact hr.trans_lt (hrx.trans hw.2)
      exact_mod_cast h
    obtain ⟨ha,hb⟩ := (data_slopeTests row hrow).2 hh
    have ha' : (0:ℝ) ≤ (row.slopeTest (63/10) 1:ℝ) := by exact_mod_cast ha
    have hb' : (0:ℝ) ≤ (row.slopeTest (-2) (-1):ℝ) := by exact_mod_cast hb
    have w := (show x∈Icc (row.lo:ℝ) row.hi from ⟨hw.1.le,hw.2.le⟩)
    have hh₁ := row.slope_bound (63/10) 1 w
    have hh₂ := row.slope_bound (-2) (-1) w
    norm_num at hh₁ hh₂
    constructor <;> linarith
  have hh₁ := chain_slope_upper data_chain values hx hy hrs.le (v:=-2)
    (fun row hrow x hw hrx _ => (data row hrow x hw hrx).2)
  have hh₂ := chain_slope_lower data_chain values hx hy hrs.le (v:=-(63/10))
    (fun row hrow x hw hrx _ => (data row hrow x hw hrx).1)
  constructor <;> linarith


theorem released_score_endpoints : EndpointData score := by
  obtain ⟨a,b,c,d,e,f,g⟩ := score_samples
  refine ⟨cast_lam ▸ score_isScoreFunction,cast_lam ▸ score_add_antitone,score_concave,?_,
    initial_slope,final_slope,a,b,c,d,e,f,g⟩
  intro x hx;simpa only [cast_lam,cast_rc,cast_zdep] using score_central (x:=x) (by simpa only [cast_rc,cast_zdep] using hx)

end StableVotingDistortion.PaperEndpoint
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open Set PaperCurve PaperBox PaperFamilies


def reducedLowSecond : Expr 2 :=
  let p := Expr.coord 0
  let w := Expr.coord 1
  let l := Expr.const (703/1250)
  let x := Expr.add p (Expr.mul w (Expr.add l (Expr.neg p)))
  .add (.add p (.neg (.mul (.atom 2 p) (.atom 1 p))))
    (.pos (.add (.add x (.neg l)) (.mul (.atom 3 p) (.atom 0 x))))

theorem eval_reducedLowSecond (φ : ℝ → ℝ) (p w : ℝ) :
    let x := p+w*(PaperMiddle.lam-p)
    eval φ ![p,w] reducedLowSecond=
      p-PaperMiddle.entry PaperMiddle.Knot.beta p*J φ p+
        max (x-PaperMiddle.lam+PaperMiddle.entry PaperMiddle.Knot.eta p*φ x) 0 := by
  simp [reducedLowSecond,eval,Expr.value,atoms,PaperMiddle.lam,sub_eq_add_neg]

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open Set PaperCurve PaperBox PaperFamilies

private def tags (z : PaperMiddle.Knot×PaperMiddle.Knot) : Prop :=
  z.1.eta*1000 ≤ 1000000000+z.1.position*z.1.beta ∧
  z.2.eta*1000 ≤ 1000000000+z.2.position*z.2.beta ∧
  (z.1.eta+z.2.eta)*1000 ≤ 2000000000+z.1.position*z.2.beta+z.2.position*z.1.beta
private instance (z : PaperMiddle.Knot×PaperMiddle.Knot) : Decidable (tags z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private theorem knot_tags : PaperMiddle.adjacentCells.all (fun z => decide (tags z))=true := by decide +kernel

private theorem cell_eta_bound {l r B D E F u : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (ha : E ≤ 1+l*B) (hb : E+F ≤ 2+l*D+r*B) (hc : F ≤ 1+r*D) :
    (1-u)*E+u*F ≤ 1+((1-u)*l+u*r)*((1-u)*B+u*D) := by
  have ha' := mul_nonneg (sq_nonneg (1-u)) (sub_nonneg.mpr ha)
  have hb' := mul_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) hu.1) (sub_nonneg.mpr hb)
  have hc' := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hc)
  linarith only [show 0 ≤ (1-u)^2*(1+l*B-E)+(1-u)*u*(2+l*D+r*B-(E+F))+u^2*(1+r*D-F) from
    add_nonneg (add_nonneg ha' hb') hc']


theorem lp_eta_bound {p : ℝ} (hp : p∈Icc PaperMiddle.pA PaperMiddle.pC) :
    PaperMiddle.entry PaperMiddle.Knot.eta p ≤ 1+p*PaperMiddle.entry PaperMiddle.Knot.beta p := by
  open PaperMiddle in
  obtain ⟨c,d,hm,hs,hk,hi⟩ := PaperMiddle.lp_cell hp
  obtain ⟨ha,hc,hb⟩ : tags (c,d) := of_decide_eq_true (List.all_eq_true.mp knot_tags _ hm)
  have ea : (c.eta:ℝ)*1000 ≤ 1000000000+(c.position:ℝ)*(c.beta:ℝ) := by exact_mod_cast ha
  have ec : (d.eta:ℝ)*1000 ≤ 1000000000+(d.position:ℝ)*(d.beta:ℝ) := by exact_mod_cast hc
  have eb : ((c.eta:ℝ)+(d.eta:ℝ))*1000 ≤ 2000000000+(c.position:ℝ)*(d.beta:ℝ)+(d.position:ℝ)*(c.beta:ℝ) := by exact_mod_cast hb
  let u := PaperMiddle.fraction p (PaperMiddle.rank c) (PaperMiddle.rank d)
  have hpos := sub_pos.mpr hs
  have h0 := div_nonneg (sub_nonneg.mpr hk.1) hpos.le
  have h1 : (p-PaperMiddle.rank c)/(PaperMiddle.rank d-PaperMiddle.rank c) ≤ 1 := (div_le_one hpos).mpr (sub_le_sub_right hk.2 _)
  have he : u=(p-PaperMiddle.rank c)/(PaperMiddle.rank d-PaperMiddle.rank c) := by
    simp only [u,PaperMiddle.fraction,min_eq_right h1,max_eq_right h0]
  have hp' : p=(1-u)*PaperMiddle.rank c+u*PaperMiddle.rank d := by
    have hz : u*(PaperMiddle.rank d-PaperMiddle.rank c)=p-PaperMiddle.rank c := by
      rw [he,div_mul_cancel₀ _ hpos.ne']
    linarith only [hz]
  rw [hi,hi]
  change (1-u)*_+u*_ ≤ 1+p*((1-u)*_+u*_)
  conv_rhs => lhs;skip
  nth_rw 1 [hp']
  apply cell_eta_bound ⟨he ▸ h0,he ▸ h1⟩
  · unfold PaperMiddle.value PaperMiddle.rank;linarith only [ea]
  · unfold PaperMiddle.value PaperMiddle.rank;linarith only [eb]
  · unfold PaperMiddle.value PaperMiddle.rank;linarith only [ec]


theorem primitive_scaled {l : ℝ} {φ : ℝ → ℝ} (hφ : IsScoreFunction l φ)
    {p q : ℝ} (hq : 0≤q) (hqp : q≤p) (hp : p≤1) : q*J φ p≤p*J φ q := by
  have ha := (primitive_sandwich hφ hq hqp hp).2
  have hb := ((eq_43_44 hφ).1 p q hq hqp hp).2.2
  linarith only [mul_le_mul_of_nonneg_left ha hq,mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hqp)]


theorem low_second_at_mass {l β η p q x : ℝ} {φ : ℝ → ℝ} (hφ : IsScoreFunction l φ)
    (hβ : 0≤β) (hη : η≤1+p*β) (hp : 0<p) (hq : q∈Icc 0 p) (hx : x∈Icc p l)
    (ht : p-β*J φ p+max (x-l+η*φ x) 0 ≤ 0) : lowSecond l φ β (-1) η p q x ≤ 0 := by
  have hx' : x∈Icc (0:ℝ) 1 := ⟨hp.le.trans hx.1,hx.2.trans hφ.lam_mem.2.le⟩
  have hs : 0≤φ x := by
    rw [← (gPhi_properties hφ).1]
    exact hφ.antitoneOn hx' ⟨hφ.lam_mem.1.le,hφ.lam_mem.2.le⟩ hx.2
  let M := max (x-l+η*φ x) 0
  have hm : M≤β*p*φ x := max_le (by
    linarith only [mul_le_mul_of_nonneg_right hη hs,hφ.le_lam_sub x hx']) (mul_nonneg (mul_nonneg hβ hp.le) hs)
  have hK := (eq_43_44 hφ).2 p q x hq.1 hq.2 hx.1 hx'.2
  have hJ := primitive_scaled hφ hq.1 hq.2 (hx.1.trans hx'.2)
  change p-β*J φ p+M≤0 at ht
  have ha := mul_nonpos_of_nonneg_of_nonpos hq.1 ht
  have hb := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq.2) (sub_nonpos.mpr hm)
  have hc := mul_le_mul_of_nonneg_left hK (mul_nonneg hp.le hβ)
  have hd := mul_le_mul_of_nonneg_left hJ hβ
  have h : p*(q+β*KP φ p q x+M)≤0 := by linarith only [ha,hb,hc,hd]
  have h' : q+β*KP φ p q x+M≤0 := by
    by_contra! hw;exact (not_lt_of_ge h) (mul_pos hp hw)
  simpa only [lowSecond,correction,show (-1:ℝ)*(l-x)=x-l by ring] using h'

theorem lp_L2_of_reduced_full {p : ℝ} (hp : p∈Icc PaperMiddle.pA PaperMiddle.lam)
    (h : ∀ w∈Icc (0:ℝ) 1,eval score ![p,w] reducedLowSecond ≤ 0) :
    BoxBound score .lp .below .L2 p := by
  have hLam : PaperMiddle.lam=lam := by norm_num [PaperMiddle.lam,lam,lamQ]
  have hp0 : 0<p := (by norm_num [PaperMiddle.pA] : 0<PaperMiddle.pA).trans_le hp.1
  have hpC := hp.2.trans (by norm_num [PaperMiddle.pC,PaperMiddle.lam] : PaperMiddle.lam≤PaperMiddle.pC)
  intro z hz hi
  have h₀ := hz 0 rfl
  have hu := hi 1 (by decide)
  have hw := hi 2 (by decide)
  let x := p+z 2*(lam-p)
  have hq : z 1*p∈Icc (0:ℝ) p := ⟨mul_nonneg hu.1 hp0.le,by simpa using mul_le_mul_of_nonneg_right hu.2 hp0.le⟩
  have pl : p≤lam := hLam ▸ hp.2
  have hx : x∈Icc p lam := ⟨by dsimp [x];linarith only [mul_nonneg hw.1 (sub_nonneg.mpr pl)],by
    dsimp [x];linarith only [mul_le_mul_of_nonneg_right hw.2 (sub_nonneg.mpr pl)]⟩
  have hb := h (z 2) hw;rw [eval_reducedLowSecond,hLam] at hb
  rw [expression_correct]
  change lowSecond PaperMiddle.lam score (PaperMiddle.entry PaperMiddle.Knot.beta (z 0)) (-1)
    (PaperMiddle.entry PaperMiddle.Knot.eta (z 0)) (z 0) (z 1*z 0) (z 0+z 2*(PaperMiddle.lam-z 0)) ≤ 0
  rw [h₀,hLam]
  exact low_second_at_mass score_isScoreFunction (PaperMiddle.entry_nonneg _ _) (lp_eta_bound ⟨hp.1,hpC⟩) hp0 hq hx hb

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve

def endConstant : ℚ := 3/50
def firstAtEnd : ℚ := (rows00.head!).qvalue endConstant


def residualCoeffs (p : Piece) : List ℚ :=
  let s := 1+6*endConstant
  [lamQ-p.lo-endConstant*(1-6*firstAtEnd)-s*p.c 0, -1-s*p.c 1,
   -s*p.c 2, -s*p.c 3, -s*p.c 4, -s*p.c 5, -s*p.c 6]

def constantTest (p : Piece) : Bool :=
  decide (lamQ < p.lo ∨ 0 ≤ lower (residualCoeffs p) (min p.hi lamQ-p.lo))

theorem constant_residual (p : Piece) (h : constantTest p = true) {x : ℝ}
    (hx : p.lo ≤ x ∧ x ≤ p.hi) (hl : x ≤ lam) :
    (endConstant:ℝ)*(1-6*((firstAtEnd:ℝ)-p.value x)) ≤ lam-x-p.value x := by
  have htest : lamQ < p.lo ∨ 0 ≤ lower (residualCoeffs p) (min p.hi lamQ-p.lo) := of_decide_eq_true h
  have hle : p.lo ≤ lamQ := by exact_mod_cast (hx.1.trans hl : (p.lo:ℝ) ≤ (lamQ:ℝ))
  have h0 := htest.resolve_left (not_lt.mpr hle)
  have hw : x-(p.lo:ℝ) ≤ ((min p.hi lamQ-p.lo:ℚ):ℝ) := by
    push_cast; exact sub_le_sub_right (le_min hx.2 hl) _
  have hlow := lower_le_horner (residualCoeffs p) (sub_nonneg.mpr hx.1) hw
  have ha : (0:ℝ) ≤ lower (residualCoeffs p) (min p.hi lamQ-p.lo) := by exact_mod_cast h0
  have hb := ha.trans hlow
  change _ ≤ (lamQ:ℝ)-x-p.value x
  have eqn : horner (residualCoeffs p) (x-p.lo) =
      (lamQ:ℝ)-x-p.value x - (endConstant:ℝ)*(1-6*((firstAtEnd:ℝ)-p.value x)) := by
    simp [residualCoeffs,Piece.value,pad,horner]
    push_cast; ring
  linarith only [hb,eqn]


def ratioCoeffs (p : Piece) : List ℚ :=
  [maxRatioQ*p.c 0+p.lo-lamQ, maxRatioQ*p.c 1+1, maxRatioQ*p.c 2,
   maxRatioQ*p.c 3, maxRatioQ*p.c 4, maxRatioQ*p.c 5, maxRatioQ*p.c 6]

def ratioTest (p : Piece) : Bool :=
  decide (rcQ < p.lo ∨ 0 ≤ lower (ratioCoeffs p) (min p.hi rcQ-p.lo))

theorem ratio_residual (p : Piece) (h : ratioTest p = true) {x : ℝ}
    (hx : p.lo ≤ x ∧ x ≤ p.hi) (hl : x ≤ rc) :
    lam-x ≤ (maxRatioQ:ℝ)*p.value x := by
  have htest : rcQ < p.lo ∨ 0 ≤ lower (ratioCoeffs p) (min p.hi rcQ-p.lo) := of_decide_eq_true h
  have hle : p.lo ≤ rcQ := by exact_mod_cast (hx.1.trans hl : (p.lo:ℝ) ≤ (rcQ:ℝ))
  have h0 := htest.resolve_left (not_lt.mpr hle)
  have hw : x-(p.lo:ℝ) ≤ ((min p.hi rcQ-p.lo:ℚ):ℝ) := by
    push_cast; exact sub_le_sub_right (le_min hx.2 hl) _
  have hlow := lower_le_horner (ratioCoeffs p) (sub_nonneg.mpr hx.1) hw
  have ha : (0:ℝ) ≤ lower (ratioCoeffs p) (min p.hi rcQ-p.lo) := by exact_mod_cast h0
  have hb := ha.trans hlow
  have eqn : horner (ratioCoeffs p) (x-p.lo) =
      (maxRatioQ:ℝ)*p.value x+x-(lamQ:ℝ) := by
    simp [ratioCoeffs,Piece.value,pad,horner]
    push_cast; ring
  change (lamQ:ℝ)-x ≤ _
  linarith only [hb,eqn]

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem valid_rows00 : rows00.all constantTest = true := by decide +kernel
private theorem valid_rows01 : rows01.all constantTest = true := by decide +kernel
private theorem valid_rows02 : rows02.all constantTest = true := by decide +kernel
private theorem valid_rows03 : rows03.all constantTest = true := by decide +kernel
private theorem valid_rows04 : rows04.all constantTest = true := by decide +kernel
private theorem valid_rows05 : rows05.all constantTest = true := by decide +kernel
private theorem valid_rows06 : rows06.all constantTest = true := by decide +kernel
private theorem valid_rows07 : rows07.all constantTest = true := by decide +kernel
private theorem valid_rows08 : rows08.all constantTest = true := by decide +kernel
private theorem valid_rows09 : rows09.all constantTest = true := by decide +kernel
private theorem valid_rows10 : rows10.all constantTest = true := by decide +kernel
private theorem valid_rows11 : rows11.all constantTest = true := by decide +kernel
private theorem valid_rows12 : rows12.all constantTest = true := by decide +kernel
private theorem valid_rows13 : rows13.all constantTest = true := by decide +kernel
private theorem valid_rows14 : rows14.all constantTest = true := by decide +kernel
private theorem valid_rows15 : rows15.all constantTest = true := by decide +kernel
private theorem valid_rows16 : rows16.all constantTest = true := by decide +kernel
private theorem valid_rows17 : rows17.all constantTest = true := by decide +kernel
private theorem valid_rows18 : rows18.all constantTest = true := by decide +kernel
private theorem valid_rows19 : rows19.all constantTest = true := by decide +kernel
private theorem valid_rows20 : rows20.all constantTest = true := by decide +kernel
private theorem valid_rows21 : rows21.all constantTest = true := by decide +kernel
private theorem valid_rows22 : rows22.all constantTest = true := by decide +kernel
private theorem valid_rows23 : rows23.all constantTest = true := by decide +kernel
private theorem valid_rows24 : rows24.all constantTest = true := by decide +kernel
private theorem valid_rows25 : rows25.all constantTest = true := by decide +kernel
private theorem valid_rows26 : rows26.all constantTest = true := by decide +kernel
private theorem valid_rows27 : rows27.all constantTest = true := by decide +kernel
private theorem valid_rows28 : rows28.all constantTest = true := by decide +kernel
private theorem valid_rows29 : rows29.all constantTest = true := by decide +kernel
private theorem valid_rows30 : rows30.all constantTest = true := by decide +kernel
private theorem valid_rows31 : rows31.all constantTest = true := by decide +kernel
private theorem valid_rows32 : rows32.all constantTest = true := by decide +kernel
private theorem valid_rows33 : rows33.all constantTest = true := by decide +kernel
private theorem valid_rows34 : rows34.all constantTest = true := by decide +kernel
private theorem valid_rows35 : rows35.all constantTest = true := by decide +kernel
private theorem valid_rows36 : rows36.all constantTest = true := by decide +kernel
private theorem valid_rows37 : rows37.all constantTest = true := by decide +kernel
private theorem valid_rows38 : rows38.all constantTest = true := by decide +kernel
private theorem valid_rows39 : rows39.all constantTest = true := by decide +kernel
private theorem valid_rows40 : rows40.all constantTest = true := by decide +kernel
private theorem valid_rows41 : rows41.all constantTest = true := by decide +kernel
private theorem valid_rows42 : rows42.all constantTest = true := by decide +kernel
private theorem valid_rows43 : rows43.all constantTest = true := by decide +kernel
private theorem valid_rows44 : rows44.all constantTest = true := by decide +kernel
private theorem valid_rows45 : rows45.all constantTest = true := by decide +kernel
private theorem valid_rows46 : rows46.all constantTest = true := by decide +kernel
private theorem valid_rows47 : rows47.all constantTest = true := by decide +kernel
private theorem valid_rows48 : rows48.all constantTest = true := by decide +kernel
private theorem valid_rows49 : rows49.all constantTest = true := by decide +kernel
private theorem valid_rows50 : rows50.all constantTest = true := by decide +kernel

theorem all_constant_valid : ∀ p ∈ pieces, constantTest p = true := by
  apply List.all_eq_true.mp
  unfold pieces
  simp only [List.all_append, valid_rows00, valid_rows01, valid_rows02, valid_rows03, valid_rows04, valid_rows05, valid_rows06, valid_rows07, valid_rows08, valid_rows09, valid_rows10, valid_rows11, valid_rows12, valid_rows13, valid_rows14, valid_rows15, valid_rows16, valid_rows17, valid_rows18, valid_rows19, valid_rows20, valid_rows21, valid_rows22, valid_rows23, valid_rows24, valid_rows25, valid_rows26, valid_rows27, valid_rows28, valid_rows29, valid_rows30, valid_rows31, valid_rows32, valid_rows33, valid_rows34, valid_rows35, valid_rows36, valid_rows37, valid_rows38, valid_rows39, valid_rows40, valid_rows41, valid_rows42, valid_rows43, valid_rows44, valid_rows45, valid_rows46, valid_rows47, valid_rows48, valid_rows49, valid_rows50, List.all_nil, Bool.and_self, Bool.true_and]
private theorem ratio_rows00 : rows00.all ratioTest = true := by decide +kernel
private theorem ratio_rows01 : rows01.all ratioTest = true := by decide +kernel
private theorem ratio_rows02 : rows02.all ratioTest = true := by decide +kernel
private theorem ratio_rows03 : rows03.all ratioTest = true := by decide +kernel
private theorem ratio_rows04 : rows04.all ratioTest = true := by decide +kernel
private theorem ratio_rows05 : rows05.all ratioTest = true := by decide +kernel
private theorem ratio_rows06 : rows06.all ratioTest = true := by decide +kernel
private theorem ratio_rows07 : rows07.all ratioTest = true := by decide +kernel
private theorem ratio_rows08 : rows08.all ratioTest = true := by decide +kernel
private theorem ratio_rows09 : rows09.all ratioTest = true := by decide +kernel
private theorem ratio_rows10 : rows10.all ratioTest = true := by decide +kernel
private theorem ratio_rows11 : rows11.all ratioTest = true := by decide +kernel
private theorem ratio_rows12 : rows12.all ratioTest = true := by decide +kernel
private theorem ratio_rows13 : rows13.all ratioTest = true := by decide +kernel
private theorem ratio_rows14 : rows14.all ratioTest = true := by decide +kernel
private theorem ratio_rows15 : rows15.all ratioTest = true := by decide +kernel
private theorem ratio_rows16 : rows16.all ratioTest = true := by decide +kernel
private theorem ratio_rows17 : rows17.all ratioTest = true := by decide +kernel
private theorem ratio_rows18 : rows18.all ratioTest = true := by decide +kernel
private theorem ratio_rows19 : rows19.all ratioTest = true := by decide +kernel
private theorem ratio_rows20 : rows20.all ratioTest = true := by decide +kernel
private theorem ratio_rows21 : rows21.all ratioTest = true := by decide +kernel
private theorem ratio_rows22 : rows22.all ratioTest = true := by decide +kernel
private theorem ratio_rows23 : rows23.all ratioTest = true := by decide +kernel
private theorem ratio_rows24 : rows24.all ratioTest = true := by decide +kernel
private theorem ratio_rows25 : rows25.all ratioTest = true := by decide +kernel
private theorem ratio_rows26 : rows26.all ratioTest = true := by decide +kernel
private theorem ratio_rows27 : rows27.all ratioTest = true := by decide +kernel
private theorem ratio_rows28 : rows28.all ratioTest = true := by decide +kernel
private theorem ratio_rows29 : rows29.all ratioTest = true := by decide +kernel
private theorem ratio_rows30 : rows30.all ratioTest = true := by decide +kernel
private theorem ratio_rows31 : rows31.all ratioTest = true := by decide +kernel
private theorem ratio_rows32 : rows32.all ratioTest = true := by decide +kernel
private theorem ratio_rows33 : rows33.all ratioTest = true := by decide +kernel
private theorem ratio_rows34 : rows34.all ratioTest = true := by decide +kernel
private theorem ratio_rows35 : rows35.all ratioTest = true := by decide +kernel
private theorem ratio_rows36 : rows36.all ratioTest = true := by decide +kernel
private theorem ratio_rows37 : rows37.all ratioTest = true := by decide +kernel
private theorem ratio_rows38 : rows38.all ratioTest = true := by decide +kernel
private theorem ratio_rows39 : rows39.all ratioTest = true := by decide +kernel
private theorem ratio_rows40 : rows40.all ratioTest = true := by decide +kernel
private theorem ratio_rows41 : rows41.all ratioTest = true := by decide +kernel
private theorem ratio_rows42 : rows42.all ratioTest = true := by decide +kernel
private theorem ratio_rows43 : rows43.all ratioTest = true := by decide +kernel
private theorem ratio_rows44 : rows44.all ratioTest = true := by decide +kernel
private theorem ratio_rows45 : rows45.all ratioTest = true := by decide +kernel
private theorem ratio_rows46 : rows46.all ratioTest = true := by decide +kernel
private theorem ratio_rows47 : rows47.all ratioTest = true := by decide +kernel
private theorem ratio_rows48 : rows48.all ratioTest = true := by decide +kernel
private theorem ratio_rows49 : rows49.all ratioTest = true := by decide +kernel
private theorem ratio_rows50 : rows50.all ratioTest = true := by decide +kernel

theorem all_ratio_valid : ∀ p ∈ pieces, ratioTest p = true := by
  apply List.all_eq_true.mp
  unfold pieces
  simp only [List.all_append, ratio_rows00, ratio_rows01, ratio_rows02, ratio_rows03, ratio_rows04, ratio_rows05, ratio_rows06, ratio_rows07, ratio_rows08, ratio_rows09, ratio_rows10, ratio_rows11, ratio_rows12, ratio_rows13, ratio_rows14, ratio_rows15, ratio_rows16, ratio_rows17, ratio_rows18, ratio_rows19, ratio_rows20, ratio_rows21, ratio_rows22, ratio_rows23, ratio_rows24, ratio_rows25, ratio_rows26, ratio_rows27, ratio_rows28, ratio_rows29, ratio_rows30, ratio_rows31, ratio_rows32, ratio_rows33, ratio_rows34, ratio_rows35, ratio_rows36, ratio_rows37, ratio_rows38, ratio_rows39, ratio_rows40, ratio_rows41, ratio_rows42, ratio_rows43, ratio_rows44, ratio_rows45, ratio_rows46, ratio_rows47, ratio_rows48, ratio_rows49, ratio_rows50, List.all_nil, Bool.and_self, Bool.true_and]

theorem constant_first : rows00.head! ∈ pieces := by decide +kernel
theorem constant_first_coords : (rows00.head!).lo = 0 ∧ endConstant ≤ (rows00.head!).hi := by decide +kernel
theorem constant_thresholds : 1 ≤ 6*firstAtEnd ∧ endConstant*6*(1+startKnot.y) ≤ lamQ := by decide +kernel

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion
open Set

theorem constant_regime_of_shape {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p0 : ℝ} (hp0 : 0 < p0) (hp0lam : p0 < lam) {β0 : ℝ} (hβ0 : 0 < β0)
    (h45a : 1 ≤ β0 * ϕ p0) (hB1 : 1 ≤ β0) (h45b : p0 * β0 * (1 + ϕ 0) ≤ lam)
    (h45c : ∀ x ∈ Set.Icc 0 lam, p0 * (1 - β0 * (ϕ p0 - ϕ x)) ≤ sigma lam ϕ x) :
    ∀ p ∈ Set.Ioc 0 p0,
      Eq37 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p ∧
        Eq38 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p := by
  intro p hp
  let B := β0
  let C := fun x => max ((1+B*p)*ϕ x-(lam-x)) 0
  have H := eq_43_44 hϕ
  have hl := hϕ.lam_mem
  have p1 : p ≤ 1 := hp.2.trans (hp0lam.le.trans hl.2.le)
  have h0 : 0 < ϕ 0 := hϕ.pos 0 ⟨le_rfl,hl.1⟩
  have hB : 0 ≤ B := hβ0.le
  have hF : 0 ≤ B*(1+ϕ 0) := by positivity
  have hlim : p * (B*(1+ϕ 0)) ≤ lam := (mul_le_mul_of_nonneg_right hp.2 hF).trans (by simpa only [mul_assoc] using h45b)
  have atq (q : ℝ) (hq : 0≤q) (hqp : q≤p) : ϕ p0 ≤ ϕ q :=
    hϕ.antitoneOn ⟨hq,hqp.trans p1⟩ ⟨hp0.le,hp0lam.le.trans hl.2.le⟩ (hqp.trans hp.2)
  have jbound (q : ℝ) (hq : 0≤q) (hqp : q≤p) : q-B*J ϕ q ≤ 0 := by
    have hj := (H.1 _ _ hq hqp p1).2.2
    have hqφ : 1 ≤ B*ϕ q := h45a.trans (mul_le_mul_of_nonneg_left (atq q hq hqp) hB)
    nlinarith only [mul_le_mul_of_nonneg_left hj hB,mul_le_mul_of_nonneg_left hqφ hq]
  have cmax (x : ℝ) (hx : x ∈ Ico 0 lam) : C x ≤ B*p*ϕ 0 := by
    have hm := hϕ.antitoneOn (show (0:ℝ)∈Icc 0 1 by norm_num) ⟨hx.1,hx.2.le.trans hl.2.le⟩ hx.1
    apply max_le
    · have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hB hp.1.le)
      nlinarith only [hh,hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hl.2.le⟩]
    · exact mul_nonneg (mul_nonneg hB hp.1.le) h0.le
  have base (q : ℝ) (hq : 0≤q) (hqp : q≤p) :
      q+B*deltaP ϕ p q+B*p*ϕ 0 ≤ lam := by
    have hh := mul_le_mul_of_nonneg_left (H.1 _ _ hq hqp p1).1 hB
    nlinarith only [hh,hlim,mul_nonneg (show 0 ≤ B-1 by linarith only [hB1]) hq]
  have lowK (q z : ℝ) (hq : 0≤q) (hqp : q≤p) (hpz : p≤z) (hz : z≤1) (hzp : 0≤ϕ z) :
      q+B*KP ϕ p q z ≤ 0 := by
    have hk := mul_le_mul_of_nonneg_left (H.2 p q z hq hqp hpz hz) hB
    have hn := mul_nonneg hB (mul_nonneg (sub_nonneg.mpr hqp) hzp)
    nlinarith only [hk,hn,jbound q hq hqp]
  constructor
  · intro x hx
    change (∀ q, 0≤q → q ≤ min p x → q+B*deltaP ϕ p q+C x ≤ lam) ∧ _
    constructor
    · intro q hq hqp
      linarith [base q hq (hqp.trans (min_le_left _ _)),cmax x hx]
    · intro q hq hqp hpx
      change q+B*KP ϕ p q x+C x ≤ 0
      dsimp only [C]
      rw [add_max]
      apply max_le
      · have hk := mul_le_mul_of_nonneg_left (H.2 p q x hq hqp hpx (hx.2.le.trans hl.2.le)) hB
        have hj := mul_le_mul_of_nonneg_left (H.1 _ _ hq hqp p1).2.2 hB
        have hsig : 0 ≤ sigma lam ϕ x := sub_nonneg.mpr (hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hl.2.le⟩)
        have hneeded : q*(1-B*(ϕ q-ϕ x)) ≤ sigma lam ϕ x := by
          have hco : 1-B*(ϕ q-ϕ x) ≤ 1-B*(ϕ p0-ϕ x) := by
            linarith [mul_le_mul_of_nonneg_left (sub_le_sub_right (atq q hq hqp) (ϕ x)) hB]
          by_cases hc : 0 ≤ 1-B*(ϕ p0-ϕ x)
          · exact (mul_le_mul_of_nonneg_left hco hq).trans
              ((mul_le_mul_of_nonneg_right (hqp.trans hp.2) hc).trans (h45c x ⟨hx.1,hx.2.le⟩))
          · exact (mul_nonpos_of_nonneg_of_nonpos hq (hco.trans (le_of_not_ge hc))).trans hsig
        unfold sigma at hneeded
        nlinarith only [hk,hj,hneeded]
      · simpa using lowK q x hq hqp hpx (hx.2.le.trans hl.2.le) (hϕ.pos x hx).le
  · intro x hx
    have hxφ := hϕ.pos x hx
    have hzero (q : ℝ) (hq : q≤p) : Wx lam ϕ x q=0 := if_pos (hq.trans (hp.2.trans hp0lam.le))
    constructor
    · intro q hq hqp
      have hb := base q hq hqp
      have hsmall : q+B*deltaP ϕ p q ≤ lam := by nlinarith only [hb,mul_nonneg (mul_nonneg hB hp.1.le) h0.le]
      change ϕ x*(q+B*deltaP ϕ p q+Wx lam ϕ x q-lam) ≤ max (-ϕ q) 0*C x
      rw [hzero q hqp,add_zero]
      exact (mul_nonpos_of_nonneg_of_nonpos hxφ.le (sub_nonpos.mpr hsmall)).trans
        (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · intro q z hq hqp hpz hz
      change ϕ x*(q+B*KP ϕ p q z+Wx lam ϕ x q-Wx lam ϕ x z) ≤ max (-ϕ z) 0*C x
      rw [hzero q hqp,add_zero]
      by_cases hzL : z≤lam
      · have hpos : 0≤ϕ z := by
          have hh := hϕ.antitoneOn ⟨hp.1.le.trans hpz,hz⟩ ⟨hl.1.le,hl.2.le⟩ hzL
          rwa [(gPhi_properties hϕ).1] at hh
        rw [show Wx lam ϕ x z=0 from if_pos hzL,sub_zero]
        exact (mul_nonpos_of_nonneg_of_nonpos hxφ.le (lowK q z hq hqp hpz hz hpos)).trans
          (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      · have hs := (gPhi_properties hϕ).2.1 z ⟨le_of_not_ge hzL,hz⟩
        have hc : (1+B*p)*ϕ x ≤ (lam-x)+C x := by
          have hh := le_max_left ((1+B*p)*ϕ x-(lam-x)) 0
          dsimp [C]; linarith
        have hk := mul_le_mul_of_nonneg_left (H.2 _ _ _ hq hqp hpz hz) hB
        have hthree := hϕ.le_lam_sub z ⟨hp.1.le.trans hpz,hz⟩
        have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB hq) hs
        have hb : q+z-lam+B*KP ϕ p q z+(1+B*p)*ϕ z ≤ 0 := by
          nlinarith only [hk,hthree,hn,jbound q hq hqp]
        have hg := mul_nonpos_of_nonneg_of_nonpos hxφ.le hb
        have hmul := mul_le_mul_of_nonpos_right hc hs
        rw [Wx,if_neg hzL,max_eq_left (neg_nonneg.mpr hs)]
        have hcancel : ϕ x*((lam-x)/ϕ x)=lam-x := by field_simp
        nlinarith only [hg,hmul,congrArg (fun r => r*ϕ z) hcancel]

end StableVotingDistortion
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set


theorem constant_masses {p : ℝ} (hp : p ∈ Ioc (0:ℝ) endConstant) :
    Eq37 lam score (fun _ => 6) (fun m x => max ((1+6*m)*score x-(lam-x)) 0) p ∧
    Eq38 lam score (fun _ => 6) (fun m x => max ((1+6*m)*score x-(lam-x)) 0) p := by
  have hfirst : score (endConstant:ℝ) = firstAtEnd := by
    rw [score_on_piece constant_first (show (endConstant:ℝ)∈Icc (rows00.head!.lo:ℝ) rows00.head!.hi by
      exact ⟨by rw [constant_first_coords.1]; norm_num [endConstant], by exact_mod_cast constant_first_coords.2⟩)]
    exact (Piece.cast_qvalue _ _).symm
  have hzero : score 0 = startKnot.y := by
    have h := select_start data_chain Piece.value Knot.y start_value
    simpa only [score,scoreEval, startKnot, Rat.cast_zero] using h
  apply constant_regime_of_shape score_isScoreFunction score_add_antitone
    (p0:=(endConstant:ℝ)) (by norm_num [endConstant]) (by norm_num [endConstant,lam,lamQ]) (by norm_num)
  · rw [hfirst]; exact_mod_cast constant_thresholds.1
  · norm_num
  · rw [hzero]; unfold lam; exact_mod_cast constant_thresholds.2
  · intro x hx
    obtain ⟨r,hr,hx'⟩ := data_chain.exists_piece (x:=x)
      (by simpa [startKnot] using hx.1)
      (by have h := hx.2.trans score_isScoreFunction.lam_mem.2.le; simpa [endKnot] using h) data_nonempty
    rw [hfirst,sigma,score_on_piece hr hx']
    exact constant_residual r (all_constant_valid _ hr) hx' hx.2
  · exact hp


theorem checked_ratio_range {x : ℝ} (hx : x∈Icc 0 rc) :
    PaperBox.ratio lam score x ∈ Icc (1:ℝ) (maxRatioQ:ℝ) := by
  have ltLam : x < lam := hx.2.trans_lt (by norm_num [rc,lam,rcQ,lamQ])
  have hpos := score_isScoreFunction.pos x ⟨hx.1,ltLam⟩
  have xmax : x ≤ 1 := ltLam.le.trans score_isScoreFunction.lam_mem.2.le
  obtain ⟨r,hr,hx'⟩ := data_chain.exists_piece (x:=x)
    (by simpa [startKnot] using hx.1) (by simpa [endKnot] using xmax) data_nonempty
  have hup := ratio_residual r (all_ratio_valid _ hr) hx' hx.2
  rw [← score_on_piece hr hx'] at hup
  refine ⟨(le_div_iff₀ hpos).mpr ?_, (div_le_iff₀ hpos).mpr hup⟩
  simpa only [one_mul] using score_isScoreFunction.le_lam_sub x ⟨hx.1,xmax⟩

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox
noncomputable section

set_option maxRecDepth 100000 in

private theorem beta_all : ∀ k∈PaperMiddle.knots,3600000 ≤ k.beta := by
  have hh : PaperMiddle.knots.all (fun k => decide (3600000 ≤ k.beta))=true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using hh

private theorem beta_lower (p : ℝ) : (18/5:ℝ) ≤ PaperMiddle.entry PaperMiddle.Knot.beta p := by
  have lookup (k : PaperMiddle.Knot) (ks : List PaperMiddle.Knot) (hk : 3600000 ≤ k.beta)
      (hs : ∀ l∈ks,3600000 ≤ l.beta) : 18/5 ≤ PaperMiddle.lookup PaperMiddle.Knot.beta p k ks := by
    induction ks generalizing k with
    | nil =>
      change 18/5 ≤ (k.beta:ℝ)/1000000
      have h : (3600000:ℝ) ≤ k.beta := by exact_mod_cast hk
      linarith
    | cons l rest ih =>
      have hl := hs l (by simp)
      rw [PaperMiddle.lookup]
      split
      · let t := PaperMiddle.fraction p (PaperMiddle.rank k) (PaperMiddle.rank l)
        have h₀ : 0 ≤ t := le_max_left _ _
        have h₁ : t ≤ 1 := max_le zero_le_one (min_le_left _ _)
        have val (u : PaperMiddle.Knot) (hu : 3600000 ≤ u.beta) : 18/5 ≤ PaperMiddle.value PaperMiddle.Knot.beta u := by
          unfold PaperMiddle.value
          have := (show (3600000:ℝ) ≤ (u.beta:ℝ) by exact_mod_cast hu)
          linarith
        have hleft := mul_le_mul_of_nonneg_left (val k hk) (sub_nonneg.mpr h₁)
        have hright := mul_le_mul_of_nonneg_left (val l hl) h₀
        change _ ≤ (1-t)*PaperMiddle.value PaperMiddle.Knot.beta k+t*PaperMiddle.value PaperMiddle.Knot.beta l
        linarith only [hleft,hright]
      · exact ih l hl (fun z hz => hs z (by simp [hz]))
  exact lookup _ _ (beta_all PaperMiddle.knots.head! (by decide +kernel)) (fun l hl => beta_all _ (List.mem_of_mem_tail hl))


theorem highFirst_of_low {φ : ℝ → ℝ} {L p β a b r : ℝ} (hφ : IsScoreFunction L φ)
    (hp : p∈Icc 0 1) (hβ : 0 ≤ β)
    (hr : r-max (a*r+b) 0 ≤ β*(1-p))
    (low : ∀ q∈Icc 0 (min p L),lowFirst L φ β a b p q L ≤ 0)
    {q : ℝ} (hq : q∈Icc 0 p) : highFirst L φ β a b p q r ≤ 0 := by
  by_cases below : q ≤ L
  · have hh := low q ⟨hq.1,le_min hq.2 below⟩
    have hc : 0 ≤ correction L φ a b L := le_max_right _ _
    have hp' := mul_nonneg (le_max_right (-φ q) 0) (le_max_right (a*r+b) 0)
    simp only [highFirst,potential,if_pos below,add_zero,lowFirst] at hh ⊢
    linarith only [hh,hc,hp']
  · have hs := hφ.le_lam_sub q ⟨hq.1,hq.2.trans hp.2⟩
    have hn : φ q ≤ 0 := by linarith only [hs,lt_of_not_ge below]
    have hd := ((eq_43_44 hφ).1 p q hq.1 hq.2 hp.2).2.1
    have hb := mul_le_mul_of_nonneg_left hd hβ
    have hsign := mul_le_mul_of_nonpos_right hr hn
    simp only [highFirst,potential,if_neg below,max_eq_left (neg_nonneg.mpr hn)]
    nlinarith only [hb,hsign]

theorem highFirst_lp {p : ℝ} (hp : p∈Icc PaperMiddle.pA PaperMiddle.pC)
    {r : ℝ} (hr : r ≤ (maxRatioQ:ℝ))
    (low : ∀ q∈Icc 0 (min p lam), lowFirst lam score (PaperMiddle.entry PaperMiddle.Knot.beta p)
      (-1) (PaperMiddle.entry PaperMiddle.Knot.eta p) p q lam ≤ 0)
    {q : ℝ} (hq : q∈Icc 0 p) :
    highFirst lam score (PaperMiddle.entry PaperMiddle.Knot.beta p) (-1) (PaperMiddle.entry PaperMiddle.Knot.eta p) p q r ≤ 0 := by
  have hp0 : p∈Icc (0:ℝ) 1 := ⟨(by norm_num [PaperMiddle.pA] : (0:ℝ) ≤ PaperMiddle.pA).trans hp.1,
    hp.2.trans (by norm_num [PaperMiddle.pC])⟩
  apply highFirst_of_low score_isScoreFunction hp0 (PaperMiddle.entry_nonneg _ _) _ low hq
  have hb := mul_le_mul_of_nonneg_right (beta_lower p) (sub_nonneg.mpr hp0.2)
  have hR : (maxRatioQ:ℝ) ≤ (18/5:ℝ)*(1-PaperMiddle.pC) := by
    norm_num [maxRatioQ,lamQ,startKnot,PaperMiddle.pC]
  linarith only [hr,hR,hp.2,hb,le_max_right ((-1:ℝ)*r+PaperMiddle.entry PaperMiddle.Knot.eta p) 0]

theorem highFirst_canonical {p β r : ℝ} (hp : p∈Icc 0 1) (hβ : 0 ≤ β)
    (low : ∀ q∈Icc 0 (min p lam), lowFirst lam score β 1 (-(β*(1-p))) p q lam ≤ 0)
    {q : ℝ} (hq : q∈Icc 0 p) : highFirst lam score β 1 (-(β*(1-p))) p q r ≤ 0 := by
  apply highFirst_of_low score_isScoreFunction hp hβ _ low hq
  have hh := le_max_left (1*r + -(β*(1-p))) 0
  linarith only [hh]

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds


def Secants (f : ℝ → ℝ) (x y : ℝ) (s : Bounds) : Prop :=
  ∃ m : ℝ, s.Holds m ∧ f y-f x = m*(y-x)

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperBox.Bounds


end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperBox.Bounds
noncomputable section


def localSlopeBox (i : Bounds) (p : Piece) : Bounds :=
  Bounds.horner p.slopeCoeffs ((i.meet ⟨p.lo,p.hi⟩).minus (point p.lo))


def slopeBounds (i : Bounds) : List Piece → Option Bounds
  | [] => none
  | p::ps =>
    if i.lo ≤ p.hi ∧ p.lo ≤ i.hi then
      match slopeBounds i ps with
      | none => some (localSlopeBox i p)
      | some t => some ((localSlopeBox i p).hull t)
    else slopeBounds i ps

def slopeBox (i : Bounds) : Bounds := (slopeBounds i pieces).getD (point 0)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperBox.Bounds
noncomputable section

theorem clamp_eq {x : ℝ} (hx : x∈Icc 0 1) : clamp x=x := by simp [clamp,min_eq_right hx.2,max_eq_right hx.1]
def totalScoreBox (i : Bounds) : Bounds := scoreBox (clampBox i)
def totalPrimitiveBox (i : Bounds) : Bounds := primitiveBox (clampBox i)
def totalScoreSlope (i : Bounds) : Bounds := (slopeBox (clampBox i)).times (clampSlopeBox i)
def totalPrimitiveSlope (i : Bounds) : Bounds := (scoreBox (clampBox i)).times (clampSlopeBox i)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open PaperBox PaperBox.Bounds Set
noncomputable section

def massE : ℚ := 1+1/20000
def baseResidual (p q : ℝ) : ℝ :=
  (massE:ℝ)*p*(J score (1-p+q)-J score q)-(lam-q)*J score p

def rankArg (b c : Bounds) : Bounds := ((point 1).minus b).plus c
def slopeP (b c : Bounds) : Bounds :=
  let x := rankArg b c
  (((point massE).times ((primitiveBox x).minus (primitiveBox c))).minus
     (((point massE).times b).times (scoreBox x))).minus (((point lamQ).minus c).times (scoreBox b))
def slopeQ (b c : Bounds) : Bounds :=
  (((point massE).times b).times ((scoreBox (rankArg b c)).minus (scoreBox c))).plus (primitiveBox b)

def validRectangle (b c : Bounds) : Prop :=
  (16/25:ℚ) ≤ b.lo ∧ b.hi ≤ (99/100:ℚ) ∧ 0 ≤ c.lo ∧ c.hi ≤ lamQ
  deriving Decidable

def qResidual (p q : ℚ) : ℚ :=
  massE*p*(qprimitive (1-p+q)-qprimitive q)-(lamQ-q)*qprimitive p

def boxAccept (b c : Bounds) : Bool :=
  let s := slopeP b c
  let t := slopeQ b c
  decide (validRectangle b c ∧ qResidual (anchor b s) (anchor c t)+deviation b s+deviation c t ≤ 0)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open PaperBox PaperBox.Bounds Set
noncomputable section


def secondResidual (p q z : ℝ) : ℝ :=
  (q+z+totalScore z-lam)*totalPrimitive p +
    (massE:ℝ)*p*(totalPrimitive (z-p+q)-totalPrimitive z-totalPrimitive q)

def secondX (p q z : Bounds) := (z.minus p).plus q
def secondK (p q z : Bounds) := (((totalPrimitiveBox (secondX p q z)).minus (totalPrimitiveBox z)).minus (totalPrimitiveBox q))
def secondA (q z : Bounds) := ((q.plus z).plus (totalScoreBox z)).minus (point lamQ)
def secondP (p q z : Bounds) :=
  (((secondA q z).times (totalPrimitiveSlope p)).plus ((point massE).times (secondK p q z))).minus
    (((point massE).times p).times (totalPrimitiveSlope (secondX p q z)))
def secondQ (p q z : Bounds) :=
  (totalPrimitiveBox p).plus (((point massE).times p).times
    ((totalPrimitiveSlope (secondX p q z)).minus (totalPrimitiveSlope q)))
def secondZ (p q z : Bounds) :=
  ((totalPrimitiveBox p).times ((point 1).plus (totalScoreSlope z))).plus
    (((point massE).times p).times ((totalPrimitiveSlope (secondX p q z)).minus (totalPrimitiveSlope z)))

def qtScore (p : ℚ) : ℚ := qscore (qclamp p)
def qtJ (p : ℚ) : ℚ := qprimitive (qclamp p)
def qSecond (p q z : ℚ) : ℚ :=
  (q+z+qtScore z-lamQ)*qtJ p + massE*p*(qtJ (z-p+q)-qtJ z-qtJ q)
def secondAccept (b c d : Bounds) : Bool :=
  let s := secondP b c d
  let t := secondQ b c d
  let v := secondZ b c d
  decide (d.hi<b.lo ∨ (d.hi=1 ∧ 0 ≤ v.lo) ∨
    qSecond (anchor b s) (anchor c t) (anchor d v)+deviation b s+deviation c t+deviation d v ≤ 0)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open PaperBox PaperBox.Bounds Set
noncomputable section

def rectTest (b : Box 2) : Bool := boxAccept (b 0) (b 1)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open PaperBox PaperBox.Bounds Set
noncomputable section

def secondRectTest (b : Box 3) : Bool := secondAccept (b 0) (b 1) (b 2)

end
end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Set
noncomputable section

def loss (φ : ℝ → ℝ) (x : ℝ) := max (-φ x) 0
def offset (lam y : ℝ) := if y ≤ lam then 0 else lam-y

theorem loss_nonneg (φ : ℝ → ℝ) (x : ℝ) : 0 ≤ loss φ x := le_max_right _ _

theorem loss_mono {φ : ℝ → ℝ} {lam x y : ℝ} (hs : IsScoreFunction lam φ)
    (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (h : x ≤ y) : loss φ x ≤ loss φ y :=
  max_le_max (neg_le_neg (hs.antitoneOn hx hy h)) le_rfl

theorem potential_linear_loss {φ : ℝ → ℝ} {lam y : ℝ} (hs : IsScoreFunction lam φ)
    (hy : y∈Icc (0:ℝ) 1) (r : ℝ) : potential lam φ r y=offset lam y+r*loss φ y := by
  have l0 := (gPhi_properties hs).1
  have hl : lam∈Icc (0:ℝ) 1 := ⟨hs.lam_mem.1.le,hs.lam_mem.2.le⟩
  by_cases h : y ≤ lam
  · have hp := hs.antitoneOn hy hl h
    rw [l0] at hp
    simp [potential,offset,loss,h,max_eq_right (neg_nonpos.mpr hp)]
  · have hn := hs.antitoneOn hl hy (le_of_not_ge h)
    rw [l0] at hn
    simp [potential,offset,loss,h,max_eq_left (neg_nonneg.mpr hn),sub_eq_add_neg]

private theorem first_form {φ : ℝ → ℝ} {lam q : ℝ} (hs : IsScoreFunction lam φ)
    (hq : q∈Icc (0:ℝ) 1) (β a b p r : ℝ) :
    highFirst lam φ β a b p q r =
      q+β*deltaP φ p q+offset lam q-lam+loss φ q*(r-max (a*r+b) 0) := by
  rw [highFirst,potential_linear_loss hs hq]; unfold loss;ring


theorem highFirst_at_max {φ : ℝ → ℝ} {lam q : ℝ} (hs : IsScoreFunction lam φ)
    (hq : q∈Icc (0:ℝ) 1) (β a b p : ℝ) (ha : a=-1 ∨ a=1) {r R : ℝ} (hr : r ≤ R) :
    highFirst lam φ β a b p q r ≤ highFirst lam φ β a b p q R := by
  rw [first_form hs hq,first_form hs hq]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (loss_nonneg _ _)
  rcases ha with rfl|rfl
  · have hmax : max (-1*R+b) 0 ≤ max (-1*r+b) 0 := max_le_max (by linarith) le_rfl
    linarith
  · have identity (x : ℝ) : x-max (1*x+b) 0=min x (-b) := by
      rcases le_total (x+b) 0 with h|h
      · simp only [one_mul,max_eq_right h,sub_zero,min_eq_left (by linarith : x ≤ -b)]
      · simp only [one_mul,max_eq_left h,min_eq_right (by linarith : -b ≤ x)];ring
    simpa only [identity] using min_le_min_right (-b) hr

private theorem second_form {φ : ℝ → ℝ} {lam q z : ℝ} (hs : IsScoreFunction lam φ)
    (hq : q∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (β a b p r : ℝ) :
    highSecond lam φ β a b p q z r = q+β*KP φ p q z+offset lam q-offset lam z+
      r*(loss φ q-loss φ z)-loss φ z*max (a*r+b) 0 := by
  rw [highSecond,potential_linear_loss hs hq,potential_linear_loss hs hz];unfold loss;ring


theorem highSecond_canonical_at_min {φ : ℝ → ℝ} {lam q z : ℝ} (hs : IsScoreFunction lam φ)
    (hq : q∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (hqz : q ≤ z)
    (β b p : ℝ) {l r : ℝ} (h : l ≤ r) :
    highSecond lam φ β 1 b p q z r ≤ highSecond lam φ β 1 b p q z l := by
  rw [second_form hs hq hz,second_form hs hq hz]
  apply sub_le_sub
  · exact add_le_add_right (mul_le_mul_of_nonpos_right h (sub_nonpos.mpr (loss_mono hs hq hz hqz))) _
  · exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (loss_nonneg _ _)


theorem highSecond_lp_at_clip {φ : ℝ → ℝ} {lam q z : ℝ} (hs : IsScoreFunction lam φ)
    (hq : q∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) (hqz : q ≤ z)
    (β b p : ℝ) {l R r : ℝ} (hr : r∈Icc l R) :
    highSecond lam φ β (-1) b p q z r ≤ 
      highSecond lam φ β (-1) b p q z (max l (min R b)) := by
  let F := highSecond lam φ β (-1) b p q z
  have up {s t : ℝ} (hst : s ≤ t) (ht : t ≤ b) : F s ≤ F t := by
    dsimp [F]
    rw [second_form hs hq hz,second_form hs hq hz,max_eq_left (by linarith : 0 ≤ -1*s+b),
      max_eq_left (by linarith : 0 ≤ -1*t+b)]
    nlinarith only [mul_le_mul_of_nonneg_right hst (loss_nonneg φ q)]
  have down {s t : ℝ} (hst : s ≤ t) (hs' : b ≤ s) : F t ≤ F s := by
    dsimp [F]
    rw [second_form hs hq hz,second_form hs hq hz,max_eq_right (by linarith : -1*t+b ≤ 0),
      max_eq_right (by linarith : -1*s+b ≤ 0)]
    simp only [mul_zero,sub_zero]
    exact add_le_add_right (mul_le_mul_of_nonpos_right hst (sub_nonpos.mpr (loss_mono hs hq hz hqz))) _
  change F r ≤ F _
  by_cases hl : b ≤ l
  · rw [min_eq_right (hl.trans (hr.1.trans hr.2)),max_eq_left hl]
    exact down hr.1 hl
  by_cases hu : R ≤ b
  · rw [min_eq_left hu,max_eq_right (hr.1.trans hr.2)]
    exact up hr.2 hu
  rw [min_eq_right (le_of_not_ge hu),max_eq_right (le_of_not_ge hl)]
  rcases le_total r b with h|h
  · exact up h le_rfl
  · exact down h le_rfl

end
end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open PaperBox.Bounds
open PaperBox (Bounds)

def abscissa (k : Knot) : ℚ := (k.position:ℚ)/1000
def ordinate (col : Knot → ℕ) (k : Knot) : ℚ := (col k:ℚ)/1000000

def clamp (i : Bounds) : Bounds :=
  ⟨max 0 (min 1 i.lo), max 0 (min 1 i.hi)⟩

def linearRange (col : Knot → ℕ) (k l : Knot) (i : Bounds) : Bounds :=
  let frac := clamp ((i.minus (point (abscissa k))).times (point ((abscissa l-abscissa k)⁻¹)))
  (point (ordinate col k)).plus (frac.times (point (ordinate col l-ordinate col k)))

def lookupRange (col : Knot → ℕ) (i : Bounds) (k : Knot) (ks : List Knot) : Bounds :=
  match ks with
  | [] => point (ordinate col k)
  | l::tail => if i.hi ≤ abscissa l then linearRange col k l i
    else if abscissa l < i.lo then lookupRange col i l tail
    else (linearRange col k l ⟨i.lo,abscissa l⟩).hull (lookupRange col ⟨abscissa l,i.hi⟩ l tail)

def entryBox (col : Knot → ℕ) (i : Bounds) : Bounds := lookupRange col i knots.head! knots.tail

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds


def checkLine (ok : Bounds → Bool) (i : Bounds) : ℕ → Bool
  | 0 => ok i
  | n+1 => if ok i then true else
    let m := (i.lo+i.hi)/2
    checkLine ok ⟨i.lo,m⟩ n && checkLine ok ⟨m,i.hi⟩ n

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
noncomputable section


private def tailPair (a b v : ℕ) (k l : Knot) : Prop :=
    (k.position ≤ b ∧ a ≤ l.position) →
    1000000000*k.position ≤ v*k.beta ∧ 1000000000*l.position ≤ v*l.beta

private instance (a b v : ℕ) (k l : Knot) : Decidable (tailPair a b v k l) := by
  unfold tailPair; infer_instance

private theorem tailBand {a b v : ℕ} {p : ℝ} (hp : p∈Icc PaperCurve.lam pC)
    (hlo : (a:ℝ)/1000≤p) (hhi : p≤(b:ℝ)/1000) (hb : (b:ℝ)/1000≤1)
    (hprim : (v:ℚ)/1000000 ≤ PaperCurve.qprimitive ((b:ℚ)/1000))
    (hrows : adjacentCells.all (fun cd => decide (tailPair a b v cd.1 cd.2))=true) :
    p ≤ entry Knot.beta p * J PaperCurve.score p := by
  obtain ⟨k,l,hm,hkl,hr,he⟩ := lp_cell (p:=p) ⟨(by norm_num [pA,PaperCurve.lam,PaperCurve.lamQ] : pA≤PaperCurve.lam).trans hp.1,hp.2⟩
  have h₁ : k.position ≤ b := by
    have h := hr.1.trans hhi
    unfold rank at h
    exact_mod_cast (by linarith : (k.position:ℝ) ≤ b)
  have h₂ : a ≤ l.position := by
    have h := hlo.trans hr.2
    unfold rank at h
    exact_mod_cast (by linarith : (a:ℝ) ≤ l.position)
  obtain ⟨e,f⟩ := (of_decide_eq_true (List.all_eq_true.mp hrows _ hm) : tailPair a b v k l) ⟨h₁,h₂⟩
  have xk : rank k ≤ (v:ℝ)/1000000 * value Knot.beta k := by
    have h : 1000000000*(k.position:ℝ) ≤ (v:ℝ)*k.beta := by exact_mod_cast e
    unfold rank value; nlinarith only [h]
  have xl : rank l ≤ (v:ℝ)/1000000 * value Knot.beta l := by
    have h : 1000000000*(l.position:ℝ) ≤ (v:ℝ)*l.beta := by exact_mod_cast f
    unfold rank value; nlinarith only [h]
  let u := fraction p (rank k) (rank l)
  have hu0 : 0 ≤ u := le_max_left _ _
  have hu1 : u ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hpos := sub_pos.mpr hkl
  have ht : u=(p-rank k)/(rank l-rank k) := by
    have hle : (p-rank k)/(rank l-rank k)≤1 := (div_le_one hpos).mpr (sub_le_sub_right hr.2 _)
    simp only [u,fraction,min_eq_right hle,
      max_eq_right (div_nonneg (sub_nonneg.mpr hr.1) hpos.le)]
  have hu : u*(rank l-rank k)=p-rank k := by rw [ht,div_mul_cancel₀ _ hpos.ne']
  have x : p ≤ (v:ℝ)/1000000 * entry Knot.beta p := by
    rw [he Knot.beta]
    change p ≤ _*((1-u)*_+u*_)
    nlinarith only [hu, mul_le_mul_of_nonneg_left xk (sub_nonneg.mpr hu1),mul_le_mul_of_nonneg_left xl hu0]
  have j : (v:ℝ)/1000000 ≤ J PaperCurve.score ((b:ℝ)/1000) := by
    have hb0 : (0:ℝ) ≤ (b:ℝ)/1000 := by positivity
    rw [PaperCurve.J_score ⟨hb0,hb⟩]
    have h := (show ((v:ℚ)/1000000:ℝ) ≤ (PaperCurve.qprimitive ((b:ℚ)/1000):ℝ) by exact_mod_cast hprim)
    rw [PaperCurve.qprimitive_exact] at h
    push_cast at h
    exact h
  apply x.trans
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (entry_nonneg _ _)
  exact j.trans (PaperCurve.primitive_decreases ⟨hp.1,hhi.trans hb⟩ ⟨hp.1.trans hhi,hb⟩ hhi)

private theorem tailRows0 : adjacentCells.all (fun cd => decide (tailPair 562 580 134955 cd.1 cd.2))=true := by decide +kernel
private theorem tailPrimitive0 : (134955:ℚ)/1000000 ≤ PaperCurve.qprimitive ((580:ℚ)/1000) := by decide +kernel
private theorem tailRows1 : adjacentCells.all (fun cd => decide (tailPair 580 600 134403 cd.1 cd.2))=true := by decide +kernel
private theorem tailPrimitive1 : (134403:ℚ)/1000000 ≤ PaperCurve.qprimitive ((600:ℚ)/1000) := by decide +kernel
private theorem tailRows2 : adjacentCells.all (fun cd => decide (tailPair 600 620 133451 cd.1 cd.2))=true := by decide +kernel
private theorem tailPrimitive2 : (133451:ℚ)/1000000 ≤ PaperCurve.qprimitive ((620:ℚ)/1000) := by decide +kernel
private theorem tailRows3 : adjacentCells.all (fun cd => decide (tailPair 620 630 132825 cd.1 cd.2))=true := by decide +kernel
private theorem tailPrimitive3 : (132825:ℚ)/1000000 ≤ PaperCurve.qprimitive ((630:ℚ)/1000) := by decide +kernel
private theorem tailRows4 : adjacentCells.all (fun cd => decide (tailPair 630 640 132099 cd.1 cd.2))=true := by decide +kernel
private theorem tailPrimitive4 : (132099:ℚ)/1000000 ≤ PaperCurve.qprimitive ((640:ℚ)/1000) := by decide +kernel

theorem lp_beta_primitive {p : ℝ} (hp : p∈Icc PaperCurve.lam pC) :
    p ≤ entry Knot.beta p * J PaperCurve.score p := by
  have h0 : (562:ℝ)/1000 ≤ p := (by norm_num [PaperCurve.lam,PaperCurve.lamQ] : (562:ℝ)/1000 ≤ PaperCurve.lam).trans hp.1
  by_cases h : p≤(580:ℝ)/1000
  · exact tailBand hp h0 h (by norm_num) tailPrimitive0 tailRows0
  have h1 := (lt_of_not_ge h).le
  clear h
  by_cases h : p≤(600:ℝ)/1000
  · exact tailBand hp h1 h (by norm_num) tailPrimitive1 tailRows1
  have h2 := (lt_of_not_ge h).le
  clear h
  by_cases h : p≤(620:ℝ)/1000
  · exact tailBand hp h2 h (by norm_num) tailPrimitive2 tailRows2
  have h3 := (lt_of_not_ge h).le
  clear h
  by_cases h : p≤(630:ℝ)/1000
  · exact tailBand hp h3 h (by norm_num) tailPrimitive3 tailRows3
  have h4 := (lt_of_not_ge h).le
  clear h
  exact tailBand hp h4 (hp.2.trans (by norm_num [pC])) (by norm_num) tailPrimitive4 tailRows4

theorem canonical_beta_primitive {p : ℝ} (hp : p∈Ioo PaperCurve.lam 1) :
    p ≤ canonical PaperCurve.score p*J PaperCurve.score p := by
  have h := (primitive_sandwich PaperCurve.score_isScoreFunction
    (PaperCurve.score_isScoreFunction.lam_mem.1.trans hp.1).le hp.2.le le_rfl).2
  rw [show J PaperCurve.score 1=0 from PaperCurve.score_isScoreFunction.integral_eq_zero] at h
  have hneg : PaperCurve.score p < 0 :=
    (PaperCurve.score_isScoreFunction.le_lam_sub p ⟨(PaperCurve.score_isScoreFunction.lam_mem.1.trans hp.1).le,hp.2.le⟩).trans_lt (sub_neg.mpr hp.1)
  have hJ : 0 < J PaperCurve.score p := by
    linarith only [h,mul_neg_of_pos_of_neg (sub_pos.mpr hp.2) hneg]
  unfold canonical
  have he : (p/J PaperCurve.score p)*J PaperCurve.score p=p := div_mul_cancel₀ _ hJ.ne'
  have eps₀ : 0 ≤ eps := by norm_num [eps]
  nlinarith only [congrArg (fun x => x*(1+eps)) he,
    mul_nonneg (PaperCurve.score_isScoreFunction.lam_mem.1.trans hp.1).le eps₀]

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open Set PaperBox
noncomputable section


def clipEta {d : ℕ} (R : ℚ) (b : Expr d) : Expr d :=
  .add (.const 1) (.pos (.add (.add b (.neg (.pos (.add b (.neg (.const R)))))) (.neg (.const 1))))

def peakSecond (m : Regime) (R : ℚ) : Expr 3 :=
  let p := Expr.coord 0
  let z := Expr.add p (.mul (.coord 2) (.add (.const 1) (.neg p)))
  fourth p (.mul (.coord 1) p) z
    (match m with | .canonical => .const 1 | _ => clipEta R (coefficients m p).b)
    (coefficients m p)

theorem eval_clipEta {d : ℕ} (φ : ℝ → ℝ) (R : ℚ) (v : Expr d) (t : Fin d → ℝ) :
    eval φ t (clipEta R v)=max 1 (min (R:ℝ) (eval φ t v)) := by
  let x := eval φ t v
  change ((1:ℚ):ℝ)+max (x+ -(max (x+ -(R:ℝ)) 0)+ -((1:ℚ):ℝ)) 0=_
  norm_num only [Rat.cast_one]
  change 1+max (x+ -(max (x+ -(R:ℝ)) 0)+ -1) 0=max 1 (min (R:ℝ) x)
  have inner : x+ -(max (x+ -(R:ℝ)) 0)=min (R:ℝ) x := by
    rcases le_total x (R:ℝ) with h|h
    · rw [max_eq_right (by linarith),min_eq_right h];ring
    · rw [max_eq_left (by linarith),min_eq_left h];ring
  rw [inner]
  rcases le_total (min (R:ℝ) x) 1 with h|h
  · rw [max_eq_right (by linarith),max_eq_left h];ring
  · rw [max_eq_left (by linarith),max_eq_right h];ring

def peakRatio (m : Regime) (φ : ℝ → ℝ) (R : ℚ) (p : ℝ) : ℝ :=
  match m with | .canonical => 1 | _ => max 1 (min (R:ℝ) (realCoeff m φ p).b)

theorem eval_peakSecond (φ : ℝ → ℝ) (m : Regime) (R : ℚ) (p u v : ℝ) :
    let c := realCoeff m φ p
    eval φ ![p,u,v] (peakSecond m R) =
      highSecond PaperMiddle.lam φ c.beta c.a c.b p (u*p) (p+v*(1-p)) (peakRatio m φ R p) := by
  cases m with
  | canonical =>
    change eval φ ![p,u,v] (reducedSecond .canonical R .one)=_
    exact eval_reducedSecond φ .canonical R .one p u v
  | lp | constant =>
    rw [peakSecond,eval_fourth]
    simp only [eval_clipEta,(eval_coeff φ ![p,u,v] (.coord 0) _).2.2,peakRatio]
    change highSecond _ _ _ _ _ _ _ (p+v*(((1:ℚ):ℝ)+ -p)) _=_
    norm_num only [Rat.cast_one,sub_eq_add_neg]
    rfl
    all_goals decide

private theorem scaled_unit {p u : ℝ} (hp : p∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) :
    u*p ∈ Icc (0:ℝ) p := ⟨mul_nonneg hu.1 hp.1,by simpa using mul_le_mul_of_nonneg_right hu.2 hp.1⟩


theorem high_of_peaks {φ : ℝ → ℝ} {R : ℚ} {p : ℝ} (m : Regime)
    (hs : IsScoreFunction PaperMiddle.lam φ) (hp : p∈Icc (0:ℝ) 1)
    (h₁ : ∀ u∈Icc (0:ℝ) 1,eval φ ![p,u] (reducedFirst m R .maximum) ≤ 0)
    (h₂ : ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,eval φ ![p,u,v] (peakSecond m R) ≤ 0) :
    (∀ k,ratioValue m φ R p k ∈ Icc 1 (R:ℝ) →
      ∀ u∈Icc (0:ℝ) 1,eval φ ![p,u] (reducedFirst m R k) ≤ 0) ∧
    (∀ k,ratioValue m φ R p k ∈ Icc 1 (R:ℝ) →
      ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,eval φ ![p,u,v] (reducedSecond m R k) ≤ 0) := by
  constructor
  · intro k hr u hu
    have e := h₁ u hu
    rw [eval_reducedFirst] at e ⊢
    have hq := scaled_unit hp hu
    exact (highFirst_at_max hs ⟨hq.1,hq.2.trans hp.2⟩ _ _ _ _
      (by cases m <;> simp [realCoeff]) hr.2).trans e
  · intro k hr u hu v hv
    have e := h₂ u hu v hv
    rw [eval_peakSecond] at e
    rw [eval_reducedSecond]
    have hq := scaled_unit hp hu
    have hv' := scaled_unit (p:=1-p) ⟨sub_nonneg.mpr hp.2,by linarith only [hp.1]⟩ hv
    have hz : p+v*(1-p) ∈ Icc (0:ℝ) 1 := ⟨add_nonneg hp.1 hv'.1,by linarith only [hv'.2]⟩
    have hqz : u*p ≤ p+v*(1-p) := le_trans hq.2 (by linarith only [hv'.1])
    have hl : u*p ∈ Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans hp.2⟩
    cases m with
    | constant => exact (highSecond_lp_at_clip hs hl hz hqz _ _ _ hr).trans e
    | lp => exact (highSecond_lp_at_clip hs hl hz hqz _ _ _ hr).trans e
    | canonical => exact (highSecond_canonical_at_min hs hl hz hqz _ _ _ hr.1).trans e

structure PeakHigh (m : Regime) (R : ℚ) (p : ℝ) : Prop where
  first : ∀ u∈Icc (0:ℝ) 1,eval PaperCurve.score ![p,u] (reducedFirst m R .maximum) ≤ 0
  second : ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,eval PaperCurve.score ![p,u,v] (peakSecond m R) ≤ 0


theorem canonical_of_peaks {R : ℚ} (hR : 1 ≤ R) {p : ℝ} (hp : p∈Icc PaperMiddle.pC PaperMiddle.p1)
    (hh : PeakHigh .canonical R p) : ReducedBoxes PaperCurve.score .canonical .above R p := by
  have hnum : PaperMiddle.lam < PaperMiddle.pC ∧ 0 ≤ PaperMiddle.pC ∧ PaperMiddle.p1 ≤ 1 := by
    norm_num [PaperMiddle.lam,PaperMiddle.pC,PaperMiddle.p1]
  have hss : IsScoreFunction PaperMiddle.lam PaperCurve.score := by
    simpa only [PaperMiddle.lam,PaperCurve.lam,PaperCurve.lamQ,Rat.cast_div,Rat.cast_ofNat] using PaperCurve.score_isScoreFunction
  have high := high_of_peaks .canonical hss ⟨hnum.2.1.trans hp.1,hp.2.trans hnum.2.2⟩ hh.first hh.second
  exact ⟨PaperAnalytic.canonical_L1_of_highFirst hp R
    (high.1 .one ⟨le_rfl,by change (1:ℝ) ≤ (R:ℝ);exact_mod_cast hR⟩),
    fun hl => ((hnum.1.trans_le hp.1).not_ge hl).elim,high.1,high.2⟩

end
end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open Set PaperBox
noncomputable section

private theorem highSecond_expanded {φ : ℝ → ℝ} {lam z : ℝ} (hs : IsScoreFunction lam φ)
    (hz : lam < z) (hz1 : z ≤ 1) {q : ℝ} (hq : q∈Icc lam z) (β a b p r : ℝ) :
    highSecond lam φ β a b p q z r =
      z+β*KP φ p q z-r*(φ q-φ z)-loss φ z*max (a*r+b) 0 := by
  have F (x : ℝ) (hx : x∈Icc lam 1) : potential lam φ r x=lam-x-r*φ x := by
    by_cases h : x=lam
    · subst x; simp [potential,(gPhi_properties hs).1]
    · exact if_neg (not_le.mpr (lt_of_le_of_ne hx.1 (Ne.symm h)))
  rw [highSecond,F q ⟨hq.1,hq.2.trans hz1⟩,F z ⟨hz.le,hz1⟩]
  unfold loss;ring


theorem highSecond_of_low_q {φ : ℝ → ℝ} {lam p q z β r : ℝ}
    (hs : IsScoreFunction lam φ) (hc : ConcaveOn ℝ (Icc lam 1) φ)
    (ha : AntitoneOn (fun x => φ x+x) (Icc lam 1))
    (hp : p∈Ioo lam 1) (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1)
    (hb : 0 ≤ β) (hm : p ≤ β*J φ p) (hr : 1 ≤ r) (a b : ℝ)
    (low : ∀ t∈Icc (0:ℝ) lam, highSecond lam φ β a b p t z r ≤ 0) :
    highSecond lam φ β a b p q z r ≤ 0 := by
  by_cases hl : q ≤ lam
  · exact low q ⟨hq.1,hl⟩
  have qh : q∈Icc lam p := ⟨le_of_not_ge hl,hq.2⟩
  have zh : lam < z := hp.1.trans_le hz.1
  have h₀ := low lam ⟨hs.lam_mem.1.le,le_rfl⟩
  rw [highSecond_expanded hs zh hz.2 ⟨le_rfl,zh.le⟩,(gPhi_properties hs).1] at h₀
  have hh := high_tail_penalty hs hc ha hp qh hz hb hm hr
    (mul_nonneg (loss_nonneg φ z) (le_max_right (a*r+b) 0))
    (by linarith only [h₀]) (gPhi_properties hs).1
  rw [highSecond_expanded hs zh hz.2 ⟨qh.1,qh.2.trans hz.1⟩]
  exact hh

private theorem named_lam : PaperMiddle.lam=PaperCurve.lam := by norm_num [PaperMiddle.lam,PaperCurve.lam,PaperCurve.lamQ]

theorem actual_peak_low_q {m : Regime} {p z q : ℝ} (hp : p∈Ioo PaperCurve.lam 1)
    (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1)
    (hm : (m=.lp ∧ p ≤ PaperMiddle.pC) ∨ m=.canonical)
    (low : ∀ t∈Icc (0:ℝ) PaperMiddle.lam,
      let c := realCoeff m PaperCurve.score p
      highSecond PaperMiddle.lam PaperCurve.score c.beta c.a c.b p t z
        (peakRatio m PaperCurve.score PaperCurve.maxRatioQ p) ≤ 0) :
    let c := realCoeff m PaperCurve.score p
    highSecond PaperMiddle.lam PaperCurve.score c.beta c.a c.b p q z
      (peakRatio m PaperCurve.score PaperCurve.maxRatioQ p) ≤ 0 := by
  have hnn {B : ℝ} (h : p ≤ B*J PaperCurve.score p) : 0 ≤ B := by
    have hp₀ := PaperCurve.score_isScoreFunction.lam_mem.1.trans hp.1
    have hg := (primitive_sandwich PaperCurve.score_isScoreFunction hp₀.le hp.2.le le_rfl).2
    rw [show J PaperCurve.score 1=0 from PaperCurve.score_isScoreFunction.integral_eq_zero] at hg
    have hφ : PaperCurve.score p < 0 := (PaperCurve.score_isScoreFunction.le_lam_sub p ⟨hp₀.le,hp.2.le⟩).trans_lt (sub_neg.mpr hp.1)
    have pos : 0 < J PaperCurve.score p := by linarith only [hg,mul_neg_of_pos_of_neg (sub_pos.mpr hp.2) hφ]
    exact nonneg_of_mul_nonneg_left (hp₀.le.trans h) pos
  have width : p ≤ (realCoeff m PaperCurve.score p).beta*J PaperCurve.score p := by
    rcases hm with ⟨rfl,hh⟩|rfl
    · exact PaperMiddle.lp_beta_primitive ⟨hp.1.le,hh⟩
    · exact PaperMiddle.canonical_beta_primitive hp
  have hr : 1 ≤ peakRatio m PaperCurve.score PaperCurve.maxRatioQ p := by
    cases m <;> first | exact le_max_left _ _ | exact le_rfl
  have hconc : ConcaveOn ℝ (Icc PaperCurve.lam 1) PaperCurve.score := by
    simpa only [PaperCurve.lam,PaperCurve.lamQ,Rat.cast_div,Rat.cast_ofNat] using PaperEndpoint.score_concave
  simp only [named_lam] at low ⊢
  exact highSecond_of_low_q PaperCurve.score_isScoreFunction hconc PaperCurve.score_add_antitone hp hq hz
    (hnn width) width hr _ _ low

end
end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperFamilies
noncomputable section

theorem canonical_reduced_of_grid
    (base : ∀ {p q : ℝ},p∈Icc (16/25:ℝ) (99/100) → q∈Icc (0:ℝ) lam →
      q+PaperMiddle.canonical score p*deltaP score p q ≤ lam)
    (second : ∀ {p q z : ℝ},p∈Icc (16/25:ℝ) (99/100) → q∈Icc (0:ℝ) lam → z∈Icc p 1 →
      highSecond lam score (PaperMiddle.canonical score p) 1 (-(PaperMiddle.canonical score p*(1-p))) p q z 1 ≤ 0)
    {p : ℝ} (hp : p∈Icc PaperMiddle.pC PaperMiddle.p1) : ReducedBoxes score .canonical .above maxRatioQ p := by
  have dp : p∈Icc (16/25:ℝ) (99/100) := hp
  have pl : lam<p := by
    have hl : lam=(703/1250:ℝ) := by norm_num [lam,lamQ]
    linarith only [dp.1,hl]
  have dp' : p∈Icc (0:ℝ) 1 := ⟨by linarith only [dp.1],by linarith only [dp.2]⟩
  have lamEq : PaperMiddle.lam=lam := by norm_num [PaperMiddle.lam,lam,lamQ]
  have hR : 1 ≤ maxRatioQ := by norm_num [maxRatioQ,lamQ,startKnot]
  have β₀ : 0 ≤ PaperMiddle.canonical score p := by
    have hb := (primitive_sandwich score_isScoreFunction dp'.1 dp'.2 le_rfl).2
    rw [show J score 1=0 from score_isScoreFunction.integral_eq_zero] at hb
    have hn := score_isScoreFunction.le_lam_sub p dp'
    have hJ : 0 ≤ J score p := by linarith only [hb,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr dp'.2) (hn.trans (sub_nonpos.mpr pl.le))]
    unfold PaperMiddle.canonical PaperMiddle.eps; positivity [dp'.1]
  have unit {u : ℝ} (hu : u∈Icc 0 1) : u*p∈Icc 0 p :=
    ⟨mul_nonneg hu.1 dp'.1,by simpa using mul_le_mul_of_nonneg_right hu.2 dp'.1⟩
  apply canonical_of_peaks hR hp
  constructor
  · intro u hu
    rw [eval_reducedFirst]
    change highFirst PaperMiddle.lam score _ 1 _ p (u*p) _ ≤ 0
    rw [lamEq]
    apply highFirst_canonical dp' β₀ _ (unit hu)
    intro q hq
    have hh := base dp ⟨hq.1,hq.2.trans (min_le_right _ _)⟩
    have hZero := (gPhi_properties score_isScoreFunction).1
    simp only [lowFirst,correction,sub_self,mul_zero,hZero,add_zero,max_self,sub_nonpos]
    exact hh
  · intro u hu v hv
    rw [eval_peakSecond]
    let z := p+v*(1-p)
    have zdom : z∈Icc p 1 := by
      have lo := mul_nonneg hv.1 (sub_nonneg.mpr dp'.2)
      have hi := mul_le_mul_of_nonneg_right hv.2 (sub_nonneg.mpr dp'.2)
      exact ⟨by dsimp [z];linarith only [lo],by dsimp [z];linarith only [hi]⟩
    apply actual_peak_low_q (m:=.canonical) ⟨pl,by linarith only [dp.2]⟩ (unit hu) zdom (Or.inr rfl)
    intro q hq
    change highSecond PaperMiddle.lam score _ 1 _ p q z 1 ≤ 0
    rw [lamEq] at hq ⊢
    exact second dp hq zdom

end
end StableVotingDistortion.PaperCurve
end

namespace StableVotingDistortion.PaperCurve
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem canonical_base_all {p q : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) PaperCurve.lam) : q+PaperMiddle.canonical score p*deltaP score p q ≤ PaperCurve.lam := by
  exact StableVotingDistortion.Lemma9Reduction.canonicalFirst hp hq
end StableVotingDistortion.PaperCurve

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory PaperBox PaperBox.Bounds
open PaperCurve (score)


def gapTest (mass s : Bounds) : Bool :=
  let after := ((point 1).minus mass).plus s
  decide (1 ≤ ((entryBox Knot.beta mass).times ((PaperCurve.scoreBox s).minus (PaperCurve.scoreBox after))).lo)

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)

def offsetPass (mass : Bounds) : Bool :=
  checkLine (gapTest mass) ⟨0,mass.hi⟩ 6

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)

def areaPass (i : Bounds) : Bool :=
  decide (((entryBox Knot.beta i).times (PaperCurve.primitiveBox ((point 1).minus i))).hi ≤ PaperCurve.lamQ)

theorem high_first_lp_verified {p q r : ℝ} (hp : p∈Icc (3/50:ℝ) (16/25)) (hq : q∈Icc 0 p)
    (hr : r≤(PaperCurve.maxRatioQ:ℝ)) :
    highFirst PaperCurve.lam score (entry Knot.beta p) (-1) (entry Knot.eta p) p q r ≤ 0 := by
  apply PaperCurve.highFirst_lp (by simpa [pA,pC] using hp) hr _ hq
  intro y hy
  exact StableVotingDistortion.Lemma9Reduction.firstLow hp
    ⟨hy.1,hy.2.trans (min_le_left _ _)⟩ ⟨PaperCurve.score_isScoreFunction.lam_mem.1.le,le_rfl⟩

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set


structure EndpointBounds (φ : ℝ → ℝ) : Prop where
  low : ∀ p ∈ Ioc 0 p0,
    Eq37 lam φ (fun _ => beta0) (fun p x => max ((1+beta0*p)*φ x-(lam-x)) 0) p ∧
    Eq38 lam φ (fun _ => beta0) (fun p x => max ((1+beta0*p)*φ x-(lam-x)) 0) p
  high : ∀ p ∈ Ico p1 1,
    Eq37 lam φ (fun p => p/J φ p) (fun p x => max (lam-x-p/J φ p*(1-p)*φ x) 0) p ∧
    Eq38 lam φ (fun p => p/J φ p) (fun p x => max (lam-x-p/J φ p*(1-p)*φ x) 0) p

private theorem change_at {φ B B' : ℝ → ℝ} {C C' : ℝ → ℝ → ℝ} {p : ℝ}
    (hb : B p=B' p) (hc : ∀ x,C p x=C' p x)
    (h : Eq37 lam φ B C p ∧ Eq38 lam φ B C p) : Eq37 lam φ B' C' p ∧ Eq38 lam φ B' C' p := by
  simpa only [Eq37,Eq38,hb,hc] using h


theorem original_verifier_of_direct_constant {φ : ℝ → ℝ} (e : PaperEndpoint.EndpointData φ)
    (hconst : ∀ p∈Ioc 0 pA,
      Eq37 lam φ (fun _ => beta0) (fun p x => max ((1+beta0*p)*φ x-(lam-x)) 0) p ∧
      Eq38 lam φ (fun _ => beta0) (fun p x => max ((1+beta0*p)*φ x-(lam-x)) 0) p)
    (hcubes : ∀ p∈Ioc pA p1,PaperBox.CubeBounds lam rc φ (beta φ p) (a p) (b φ p) p) :
    VerifierHypotheses lam φ (beta φ) (corr φ) ∧ 1+2*lam≤2.1248 := by
  have eqs (p : ℝ) (hp : p∈Ioo 0 1) : Eq37 lam φ (beta φ) (corr φ) p ∧ Eq38 lam φ (beta φ) (corr φ) p := by
    by_cases ha : p≤pA
    · have hc : p≤pC := ha.trans (by norm_num [pA,pC])
      apply change_at (h:=hconst p ⟨hp.1,ha⟩)
      · simp [beta,ha]
      · intro x;simp [corr,PaperBox.correction,a,b,hc,ha];ring_nf
    by_cases hm : p≤p1
    · apply PaperBox.cubes_imply_eq37_eq38 (lam:=lam) (rc:=rc) e.score.pos _ (hcubes p ⟨lt_of_not_ge ha,hm⟩)
      intro x hx;exact e.line x ⟨hx.1,hx.2.trans (by norm_num [lam])⟩
    · have hC : ¬p≤pC := fun h => hm (h.trans (by norm_num [pC,p1]))
      apply change_at (h:=PaperEndpoint.high_extension e p ⟨le_of_not_ge hm,hp.2⟩)
      · simp [beta,ha,hC,hm]
      · intro x;simp [corr,PaperBox.correction,a,b,beta,hC,ha,hm,lam];ring_nf
  exact ⟨⟨e.score,e.decreasing,fun _ hp => beta_nonneg e.score hp,fun _ _ _ _ => le_max_right _ _,
    fun p hp => (eqs p hp).1,fun p hp => (eqs p hp).2⟩,by norm_num [lam]⟩

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle


theorem named_witness_of_reduced
    (he : PaperEndpoint.EndpointData PaperCurve.score)
    (hm : PaperFamilies.ReducedRanges PaperCurve.score PaperCurve.maxRatioQ) :
    VerifierHypotheses lam PaperCurve.score (beta PaperCurve.score) (corr PaperCurve.score) ∧
      1+2*lam≤2.1248 := by
  have hpa : (PaperCurve.endConstant:ℝ)=pA := by norm_num [PaperCurve.endConstant,pA]
  have hl : PaperCurve.lam=lam := by norm_num [PaperCurve.lam,PaperCurve.lamQ,lam]
  have hrc : PaperCurve.rc=rc := by norm_num [PaperCurve.rc,PaperCurve.rcQ,rc]
  have hr (x : ℝ) (hx : x∈Set.Icc 0 rc) : PaperBox.ratio lam PaperCurve.score x∈Set.Icc 1 (PaperCurve.maxRatioQ:ℝ) := by
    simpa only [hl] using PaperCurve.checked_ratio_range (x:=x) (hrc.symm ▸ hx)
  have h0 := hr 0 (by norm_num [rc])
  apply original_verifier_of_direct_constant he _ (fun _ hp => PaperFamilies.cubes_of_reduced_ranges hm (h0.1.trans h0.2) hr hp)
  intro p hp
  simpa only [hl,beta0] using PaperCurve.constant_masses (p:=p) (hpa.symm ▸ hp)


theorem named_witness_of_middle_boxes
    (h : PaperFamilies.ReducedRanges PaperCurve.score PaperCurve.maxRatioQ) :
    VerifierHypotheses lam PaperCurve.score (beta PaperCurve.score) (corr PaperCurve.score) ∧
      1+2*lam≤2.1248 :=
  named_witness_of_reduced PaperEndpoint.released_score_endpoints h

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open Set PaperBox
open PaperCurve (score maxRatioQ)

theorem reduced_lp_from_physical (s : Side) {p : ℝ} (hp : p∈Icc PaperMiddle.pA PaperMiddle.pC)
    (l₁ : BoxBound score .lp s .L1 p) (l₂ : p≤PaperMiddle.lam → BoxBound score .lp s .L2 p)
    (h₂ : ∀ q∈Icc (0:ℝ) p, ∀ z∈Icc p 1, ∀ r∈Icc (1:ℝ) (maxRatioQ:ℝ),
      highSecond PaperMiddle.lam score (PaperMiddle.entry PaperMiddle.Knot.beta p) (-1)
        (PaperMiddle.entry PaperMiddle.Knot.eta p) p q z r ≤ 0) :
    ReducedBoxes score .lp s maxRatioQ p := by
  have hd : p∈Icc (3/50:ℝ) (16/25) := by simpa [PaperMiddle.pA,PaperMiddle.pC] using hp
  have pos : 0≤p := (by norm_num : (0:ℝ)≤3/50).trans hd.1
  have one : p≤1 := hd.2.trans (by norm_num)
  have qdom {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : u*p∈Icc (0:ℝ) p :=
    ⟨mul_nonneg hu.1 pos,by simpa using mul_le_mul_of_nonneg_right hu.2 pos⟩
  refine ⟨l₁,l₂,?_,?_⟩
  · intro k hr u hu
    rw [eval_reducedFirst]
    have lam_eq : PaperCurve.lam=PaperMiddle.lam := by norm_num [PaperMiddle.lam,PaperCurve.lam,PaperCurve.lamQ]
    simpa only [realCoeff,lam_eq] using PaperMiddle.high_first_lp_verified hd (qdom hu) hr.2
  · intro k hr u hu v hv
    rw [eval_reducedSecond]
    apply h₂ _ (qdom hu) _ _ _ hr
    exact ⟨by linarith only [mul_nonneg hv.1 (sub_nonneg.mpr one)],
      by linarith only [mul_le_mul_of_nonneg_right hv.2 (sub_nonneg.mpr one)]⟩

end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperFamilies
open Set PaperBox
open PaperCurve (score)

theorem original_lp_low_of_physical
    (h : ∀ {p q x : ℝ}, p∈Icc (3/50:ℝ) (16/25) → q∈Icc (0:ℝ) p → x∈Icc (0:ℝ) PaperCurve.lam →
      lowFirst PaperCurve.lam score (PaperMiddle.entry PaperMiddle.Knot.beta p) (-1)
        (PaperMiddle.entry PaperMiddle.Knot.eta p) p q x ≤ 0)
    (s : Side) {p : ℝ} (hp : p∈Icc PaperMiddle.pA PaperMiddle.pC)
    (hs : match s with | .below => p≤PaperMiddle.lam | .above => PaperMiddle.lam≤p) :
    BoxBound score .lp s .L1 p := by
  have dom : p∈Icc (3/50:ℝ) (16/25) := by simpa [PaperMiddle.pA,PaperMiddle.pC] using hp
  have lp : PaperCurve.lam = PaperMiddle.lam := by norm_num [PaperCurve.lam,PaperCurve.lamQ,PaperMiddle.lam]
  intro t ht hdom
  rw [expression_correct]
  have z := ht (0:Fin 3) (by decide)
  have u := hdom (1:Fin 3) (by decide)
  have w := hdom (2:Fin 3) (by decide)
  have f (m : ℝ) (hmp : m≤p) (hm0 : 0 ≤ m) (hml : m≤PaperMiddle.lam) :
      lowFirst PaperMiddle.lam score (PaperMiddle.entry PaperMiddle.Knot.beta p) (-1)
        (PaperMiddle.entry PaperMiddle.Knot.eta p) p (t 1*m)
        (t 1*m+t 2*(PaperMiddle.lam-t 1*m))≤0 := by
    have hq₀ := mul_nonneg u.1 hm0
    have hq₁ : t 1*m ≤ m := by simpa using mul_le_mul_of_nonneg_right u.2 hm0
    have hlen : 0≤PaperMiddle.lam-t 1*m := sub_nonneg.mpr (hq₁.trans hml)
    have xdom : t 1*m+t 2*(PaperMiddle.lam-t 1*m)∈Icc (0:ℝ) PaperMiddle.lam :=
      ⟨add_nonneg hq₀ (mul_nonneg w.1 hlen),by linarith only [mul_le_mul_of_nonneg_right w.2 hlen]⟩
    simpa only [lp] using (h dom ⟨hq₀,hq₁.trans hmp⟩ (lp.symm ▸ xdom))
  cases s with
  | below =>
    change lowFirst PaperMiddle.lam score (PaperMiddle.entry PaperMiddle.Knot.beta (t 0)) (-1)
        (PaperMiddle.entry PaperMiddle.Knot.eta (t 0)) (t 0) (t 1*t 0)
        (t 1*t 0+t 2*(PaperMiddle.lam-t 1*t 0))≤0
    rw [z]
    exact f p le_rfl ((by norm_num : (0:ℝ)≤3/50).trans dom.1) hs
  | above =>
    change lowFirst PaperMiddle.lam score (PaperMiddle.entry PaperMiddle.Knot.beta (t 0)) (-1)
        (PaperMiddle.entry PaperMiddle.Knot.eta (t 0)) (t 0) (t 1*PaperMiddle.lam)
        (t 1*PaperMiddle.lam+t 2*(PaperMiddle.lam-t 1*PaperMiddle.lam))≤0
    rw [z]
    exact f PaperMiddle.lam hs (by norm_num [PaperMiddle.lam]) le_rfl

end StableVotingDistortion.PaperFamilies
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperFamilies
open PaperCurve (score maxRatioQ)

theorem middle_ranges_from_inequalities
    (first : ∀ {p q x : ℝ}, p∈Icc (3/50:ℝ) (16/25) → q∈Icc (0:ℝ) p → x∈Icc (0:ℝ) PaperCurve.lam →
      lowFirst PaperCurve.lam score (entry Knot.beta p) (-1) (entry Knot.eta p) p q x ≤ 0)
    (second : ∀ {p : ℝ}, p∈Icc pA lam → BoxBound score .lp .below .L2 p)
    (high : ∀ {p q z r : ℝ}, p∈Icc pA pC → q∈Icc 0 p → z∈Icc p 1 → r∈Icc 1 (maxRatioQ:ℝ) →
      highSecond lam score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z r ≤ 0)
    (canonical : ∀ {p : ℝ}, p∈Icc pC p1 → ReducedBoxes score .canonical .above maxRatioQ p) :
    ReducedRanges score maxRatioQ := by
  have ha : pA ≤ lam ∧ lam ≤ pC := by norm_num [pA,lam,pC]
  constructor
  · intro p hp
    have hm : p∈Icc pA pC := ⟨hp.1.le,hp.2.trans ha.2⟩
    apply reduced_lp_from_physical .below hm (original_lp_low_of_physical first .below hm hp.2)
      (fun _ => second ⟨hp.1.le,hp.2⟩)
    exact fun _ hq _ hz _ hr => high hm hq hz hr
  · intro p hp
    have hm : p∈Icc pA pC := ⟨ha.1.trans hp.1.le,hp.2⟩
    apply reduced_lp_from_physical .above hm (original_lp_low_of_physical first .above hm hp.1.le)
      (fun hl => (hp.1.not_ge hl).elim)
    exact fun _ hq _ hz _ hr => high hm hq hz hr
  · intro p hp
    exact canonical ⟨hp.1.le,hp.2⟩

end StableVotingDistortion.PaperMiddle
end

namespace StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem low_first_lp_verified {p q x : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hq : q ∈ Icc (0:ℝ) p) (hx : x ∈ Icc (0:ℝ) PaperCurve.lam) : lowFirst PaperCurve.lam score (entry PaperMiddle.Knot.beta p) (-1) (entry PaperMiddle.Knot.eta p) p q x ≤ 0 := by
  exact StableVotingDistortion.Lemma9Reduction.firstLow hp hq hx
end StableVotingDistortion.PaperMiddle

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds


end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Bounds

def contactSlope (t : ℚ) (left right : Bounds → Bounds) (i : Bounds) : Bounds :=
  if i.hi ≤ t then left i else if t ≤ i.lo then right i
  else (left ⟨i.lo,t⟩).hull (right ⟨t,i.hi⟩)

end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
noncomputable section

private def ray (col : Knot → ℕ) (k l : Knot) (p : ℝ) : ℝ :=
  if p ≤ (qRank k:ℝ) then value col k else value col k+(qSlope col k l:ℝ)*(p-rank k)

def raySlope (col : Knot → ℕ) (k l : Knot) : Bounds → Bounds :=
  contactSlope (qRank k) (fun _ => point 0) (fun _ => point (qSlope col k l))

private theorem start_value (col : Knot → ℕ) (k : Knot) (ks : List Knot)
    (h : (k::ks).IsChain (fun a b => a.position < b.position)) :
    lookup col (rank k) k ks=value col k := by
  cases ks with
  | nil => rfl
  | cons l tail =>
    have hkl : rank k < rank l := div_lt_div_of_pos_right (by exact_mod_cast h.rel) (by norm_num)
    simp [lookup, hkl.le,interpolate_eq _ _ _ _ hkl ⟨le_rfl,hkl.le⟩]


def lookupSlope (col : Knot → ℕ) (k : Knot) (ks : List Knot) : Bounds → Bounds :=
  match ks with
  | [] => fun _ => point 0
  | l::tail => contactSlope (qRank l) (raySlope col k l) (lookupSlope col l tail)

def entrySlope (col : Knot → ℕ) (i : Bounds) : Bounds := lookupSlope col knots.head! knots.tail i

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox.Bounds

def chooseAt (t : ℚ) (x left right : Bounds) : Bounds :=
  if x.hi ≤ t then left else if t < x.lo then right else left.hull right

end StableVotingDistortion.PaperBox.Bounds
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox
open Set
noncomputable section


theorem highSecond_low_form {φ : ℝ → ℝ} {L q z : ℝ} (hs : IsScoreFunction L φ)
    (hq : q ≤ L) (hz : z∈Icc (0:ℝ) 1) (β a b p r : ℝ) :
    highSecond L φ β a b p q z r =
      q+β*KP φ p q z+max (z-L) 0 -loss φ z*(r+max (a*r+b) 0) := by
  have off : offset L z= -max (z-L) 0 := by
    by_cases h : z≤L
    · simp [offset,h,max_eq_right (sub_nonpos.mpr h)]
    · rw [offset,if_neg h,max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  rw [highSecond,potential_linear_loss hs hz r,off,show potential L φ r q=0 from if_pos hq]
  unfold loss;ring


theorem highSecond_lp_low_peak {φ : ℝ → ℝ} {L q z : ℝ} (hs : IsScoreFunction L φ)
    (hq : q ≤ L) (hz : z∈Icc (0:ℝ) 1) (β b p R : ℝ) (hR : 1 ≤ R) :
    highSecond L φ β (-1) b p q z (max 1 (min R b)) =
      q+β*KP φ p q z+max (z-L) 0 -loss φ z*max 1 b := by
  rw [highSecond_low_form hs hq hz]
  have id (r : ℝ) : r+max (-1*r+b) 0=max r b := by
    rcases le_total b r with h|h
    · rw [max_eq_right (by linarith),max_eq_left h];ring
    · rw [max_eq_left (by linarith),max_eq_right h];ring
  rw [id,max_assoc,max_eq_right (min_le_right R b)]


end
end StableVotingDistortion.PaperBox
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (totalPrimitive totalPrimitiveBox totalPrimitiveSlope totalScore totalScoreBox totalScoreSlope)
noncomputable section

def penaltyBox (i : Bounds) : Bounds := (point 1).plus (((entryBox Knot.eta i).minus (point 1)).posPart)
def penaltySlope (i : Bounds) : Bounds :=
  (clipSlope ((entryBox Knot.eta i).minus (point 1))).times (entrySlope Knot.eta i)

def physicalKBox (p q z : Bounds) : Bounds :=
  ((totalPrimitiveBox (physicalXBox p q z)).minus (totalPrimitiveBox z)).minus (totalPrimitiveBox q)

def physicalP (i j k : Bounds) : Bounds :=
  (((entrySlope Knot.beta i).times (physicalKBox i j k)).minus
    ((entryBox Knot.beta i).times (totalPrimitiveSlope (physicalXBox i j k)))).plus
    ((penaltySlope i).times (totalScoreBox k))
def physicalQ (i j k : Bounds) : Bounds :=
  (point 1).plus ((entryBox Knot.beta i).times
    ((totalPrimitiveSlope (physicalXBox i j k)).minus (totalPrimitiveSlope j)))
def physicalZ (i j k : Bounds) : Bounds :=
  ((point 1).plus ((entryBox Knot.beta i).times
    ((totalPrimitiveSlope (physicalXBox i j k)).minus (totalPrimitiveSlope k)))).plus
    ((penaltyBox i).times (totalScoreSlope k))

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox
noncomputable section

theorem penaltyLP_eq (p : ℝ) : penaltyLP p=max 1 (entry Knot.eta p) := by
  unfold penaltyLP
  rcases le_total (entry Knot.eta p) 1 with h|h
  · rw [max_eq_right (sub_nonpos.mpr h),max_eq_left h];ring
  · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right h];ring

private theorem totalJ_eq {x : ℝ} (h : x∈Icc (0:ℝ) 1) : PaperCurve.totalPrimitive x=J PaperCurve.score x := by
  simp [PaperCurve.totalPrimitive,PaperCurve.clamp_eq h]

theorem physical_eq_form {p q z : ℝ} (hp : p∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1)
    (hl : PaperCurve.lam ≤ z) :
    physicalResidual p q z=q+entry Knot.beta p*KP PaperCurve.score p q z+max (z-PaperCurve.lam) 0-
      loss PaperCurve.score z*max 1 (entry Knot.eta p) := by
  have z0 : z∈Icc (0:ℝ) 1 := ⟨hp.1.trans hz.1,hz.2⟩
  have q0 : q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans hp.2⟩
  have x0 : z-p+q∈Icc (0:ℝ) 1 := ⟨by linarith only [hz.1,hq.1],by linarith only [hq.2,hz.2]⟩
  have hφ : PaperCurve.score z ≤ 0 :=
    (PaperCurve.score_isScoreFunction.le_lam_sub z z0).trans (sub_nonpos.mpr hl)
  simp only [physicalResidual,physicalK,totalJ_eq x0,totalJ_eq q0,totalJ_eq z0,
    PaperCurve.totalScore,PaperCurve.clamp_eq z0,penaltyLP_eq,KP,loss,
    max_eq_left (sub_nonneg.mpr hl),max_eq_left (neg_nonneg.mpr hφ)]
  ring


theorem physical_at_one {p q : ℝ} (hp : p∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) p)
    (h1 : lowFirst PaperCurve.lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p)
      p q PaperCurve.lam ≤ 0) : physicalResidual p q 1 ≤ 0 := by
  have hs := PaperCurve.score_isScoreFunction
  rw [physical_eq_form hp hq ⟨hp.2,le_rfl⟩ hs.lam_mem.2.le]
  have hh : KP PaperCurve.score p q 1=deltaP PaperCurve.score p q := by
    simp [KP,deltaP,show J PaperCurve.score 1=0 from hs.integral_eq_zero]
  rw [hh,loss,hs.at_one,max_eq_left (sub_nonneg.mpr hs.lam_mem.2.le)]
  unfold lowFirst at h1
  have hz : 0 ≤ correction PaperCurve.lam PaperCurve.score (-1) (entry Knot.eta p) PaperCurve.lam := le_max_right _ _
  have hb := le_max_left (1:ℝ) (entry Knot.eta p)
  norm_num only [neg_neg,max_eq_left zero_le_one,one_mul]
  linarith only [h1,hz,hb]


theorem physical_at_one_verified {p q : ℝ} (hp : p∈Icc pA pC)
    (hq : q∈Icc (0:ℝ) (min p PaperCurve.lam)) : physicalResidual p q 1 ≤ 0 := by
  have hp₀ : p∈Icc (0:ℝ) 1 := ⟨(by norm_num [pA] : (0:ℝ) ≤ pA).trans hp.1,
    hp.2.trans (by norm_num [pC])⟩
  have hqp : q∈Icc (0:ℝ) p := ⟨hq.1,hq.2.trans (min_le_left _ _)⟩
  have hqL := hq.2.trans (min_le_right _ _)
  have htop := high_first_lp_verified hp hqp (r:=0) (by norm_num [PaperCurve.maxRatioQ,PaperCurve.lamQ,PaperCurve.startKnot])
  have hφ : 0 ≤ PaperCurve.score q := by
    have he := PaperCurve.score_antitone (a:=q) (b:=PaperCurve.lam)
      ⟨hq.1,hqp.2.trans hp₀.2⟩ ⟨PaperCurve.score_isScoreFunction.lam_mem.1.le,PaperCurve.score_isScoreFunction.lam_mem.2.le⟩ hqL
    rwa [(gPhi_properties PaperCurve.score_isScoreFunction).1] at he
  simp only [highFirst,potential,if_pos hqL,max_eq_right (neg_nonpos.mpr hφ),zero_mul,sub_zero,add_zero] at htop
  apply physical_at_one hp₀ hqp
  simpa [lowFirst,correction,(gPhi_properties PaperCurve.score_isScoreFunction).1] using htop


theorem highSecond_below_of_low {p q z r : ℝ} (hp : p∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) p)
    (hz : z∈Icc p PaperCurve.lam)
    (h2 : lowSecond PaperCurve.lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z ≤ 0) :
    highSecond PaperCurve.lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z r ≤ 0 := by
  have hqL := hq.2.trans (hz.1.trans hz.2)
  have hnonneg : 0 ≤ correction PaperCurve.lam PaperCurve.score (-1) (entry Knot.eta p) z := le_max_right _ _
  have hd := mul_nonneg (le_max_right (-PaperCurve.score z) 0) (le_max_right ((-1:ℝ)*r+entry Knot.eta p) 0)
  rw [highSecond,potential,if_pos hqL,potential,if_pos hz.2]
  unfold lowSecond at h2
  linarith only [h2,hnonneg,hd]

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (anchor deviation qtScore qtJ)
noncomputable section

def rationalRay (col : Knot → ℕ) (p : ℚ) (k l : Knot) : ℚ :=
  let t := max 0 (min 1 ((p-qRank k)/(qRank l-qRank k)))
  (1-t)*qValue col k+t*qValue col l

def rationalLookup (col : Knot → ℕ) (p : ℚ) (k : Knot) : List Knot → ℚ
  | [] => qValue col k
  | l::ks => if p ≤ qRank l then rationalRay col p k l else rationalLookup col p l ks

def rationalEntry (col : Knot → ℕ) (p : ℚ) : ℚ := rationalLookup col p knots.head! knots.tail

def rationalPhysical (p q z : ℚ) : ℚ :=
  q+rationalEntry Knot.beta p*(qtJ (z-p+q)-qtJ z-qtJ q)+z-PaperCurve.lamQ+
    (1+max (rationalEntry Knot.eta p-1) 0)*qtScore z

def physicalAccept (b c d : Bounds) : Bool :=
  let s := physicalP b c d
  let t := physicalQ b c d
  let v := physicalZ b c d
  decide (d.hi < b.lo ∨ b.hi < c.lo ∨ (d.hi=1 ∧ 0 ≤ v.lo) ∨
    rationalPhysical (anchor b s) (anchor c t) (anchor d v)+deviation b s+deviation c t+deviation d v ≤ 0)

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
noncomputable section

def physicalRectTest (b : Box 3) : Bool := physicalAccept (b 0) (b 1) (b 2)

theorem all_physical_of_cells (all : ∀ cd∈adjacentCells,CellCovered cd.1 cd.2)
    {p q z : ℝ} (hp : p∈Icc pA pC) (hq : q∈Icc 0 (min p PaperCurve.lam))
    (hz : z∈Icc (max p PaperCurve.lam) 1) (base : physicalResidual p q 1 ≤ 0) :
    physicalResidual p q z ≤ 0 := by
  obtain ⟨k,l,hm,_,hd,_⟩ := lp_cell hp
  exact all (k,l) hm p q z hd hq hz base

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperFamilies
noncomputable section

private theorem lam_agrees : lam=PaperCurve.lam := by norm_num [lam,PaperCurve.lam,PaperCurve.lamQ]


theorem highSecond_from_physical {p q z r : ℝ} (hp : p∈Icc pA pC)
    (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1) (hr : r∈Icc 1 (PaperCurve.maxRatioQ:ℝ))
    (hL : ∀ q'∈Icc (0:ℝ) p,∀ z'∈Icc p PaperCurve.lam,
      lowSecond PaperCurve.lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q' z' ≤ 0)
    (all : ∀ cd∈adjacentCells,CellCovered cd.1 cd.2) :
    highSecond lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z r ≤ 0 := by
  have hp₀ : p∈Icc (0:ℝ) 1 := ⟨(by norm_num [pA] : (0:ℝ) ≤ pA).trans hp.1,hp.2.trans (by norm_num [pC])⟩
  have hq₀ : q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans hp₀.2⟩
  have hz₀ : z∈Icc (0:ℝ) 1 := ⟨hp₀.1.trans hz.1,hz.2⟩
  let peak : ℝ := max 1 (min (PaperCurve.maxRatioQ:ℝ) (entry Knot.eta p))
  have low (t : ℝ) (ht : t∈Icc (0:ℝ) (min p PaperCurve.lam)) :
      highSecond PaperCurve.lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p t z peak ≤ 0 := by
    have htp : t∈Icc (0:ℝ) p := ⟨ht.1,ht.2.trans (min_le_left _ _)⟩
    by_cases hzl : z ≤ PaperCurve.lam
    · exact highSecond_below_of_low hp₀ htp ⟨hz.1,hzl⟩ (hL t htp z ⟨hz.1,hzl⟩)
    · have hlz := le_of_not_ge hzl
      have pos := all_physical_of_cells all hp ht ⟨max_le hz.1 hlz,hz.2⟩ (physical_at_one_verified hp ht)
      rw [physical_eq_form hp₀ htp hz hlz] at pos
      rw [highSecond_lp_low_peak PaperCurve.score_isScoreFunction (ht.2.trans (min_le_right _ _)) hz₀ _ _ _ _ (hr.1.trans hr.2)]
      exact pos
  rw [lam_agrees]
  apply (highSecond_lp_at_clip PaperCurve.score_isScoreFunction hq₀ hz₀ (hq.2.trans hz.1) _ _ _ hr).trans
  by_cases hpl : p ≤ PaperCurve.lam
  · exact low q ⟨hq.1,le_min hq.2 (hq.2.trans hpl)⟩
  have hpi : p∈Ioo PaperCurve.lam 1 := ⟨lt_of_not_ge hpl,hp.2.trans_lt (by norm_num [pC])⟩
  have hh := actual_peak_low_q (m:=.lp) hpi hq hz (Or.inl ⟨rfl,hp.2⟩) (by
    intro t ht
    rw [lam_agrees] at ht ⊢
    exact low t ⟨ht.1,le_min (ht.2.trans hpi.1.le) ht.2⟩)
  simpa only [lam_agrees,realCoeff,peakRatio] using hh

end
end StableVotingDistortion.PaperMiddle
end

namespace StableVotingDistortion.PaperAnalytic
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
open PaperFamilies
theorem released_low_second {p x : ℝ} (hp : p ∈ Icc pA PaperCurve.lam) (hx : x ∈ Icc p PaperCurve.lam) : p-entry PaperMiddle.Knot.beta p*J score p+max (x-PaperCurve.lam+entry PaperMiddle.Knot.eta p*score x) 0≤0 := by exact StableVotingDistortion.Lemma9Reduction.secondLow hp hx
theorem released_lp_L2 {p : ℝ} (hp : p∈Icc pA PaperMiddle.lam) : BoxBound score .lp .below .L2 p := by
  apply lp_L2_of_reduced_full hp
  intro w hw
  rw [eval_reducedLowSecond]
  have el : PaperMiddle.lam=PaperCurve.lam := by norm_num [PaperMiddle.lam,PaperCurve.lam,lamQ]
  rw [el] at hp ⊢
  apply released_low_second hp
  exact ⟨by linarith only [mul_nonneg hw.1 (sub_nonneg.mpr hp.2)],
    by linarith only [mul_le_mul_of_nonneg_right hw.2 (sub_nonneg.mpr hp.2)]⟩

end StableVotingDistortion.PaperAnalytic
section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperFamilies
noncomputable section


theorem released_lp_high_second_of_cells (cells : ∀ cd∈adjacentCells, CellCovered cd.1 cd.2)
    {p q z r : ℝ} (hp : p∈Icc pA pC)
    (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1) (hr : r∈Icc 1 (PaperCurve.maxRatioQ:ℝ)) :
    highSecond lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z r ≤ 0 := by
  apply highSecond_from_physical hp hq hz hr _ cells
  intro t ht x hx
  have hl : lam=PaperCurve.lam := by norm_num [lam,PaperCurve.lam,PaperCurve.lamQ]
  obtain ⟨u,hu,he⟩ := affine_parameter (lo:=0) ht
  obtain ⟨w,hw,hw'⟩ := affine_parameter hx
  simp only [zero_add,sub_zero] at he
  have pL := hx.1.trans hx.2
  have H := PaperAnalytic.released_lp_L2 (p:=p) ⟨hp.1,by rwa [hl]⟩ ![p,u,w]
    (by intro i hi;fin_cases i <;> simp_all) (by intro i hi;fin_cases i <;> simp_all)
  rw [expression_correct PaperCurve.score .lp .below .L2 ![p,u,w]] at H
  change lowSecond lam PaperCurve.score _ _ _ p (u*p) (p+w*(lam-p)) ≤ 0 at H
  simpa only [realCoeff,Matrix.cons_val_zero,hl,← he,← hw'] using H

end
end StableVotingDistortion.PaperMiddle
end

namespace StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem physical_lp_cells : ∀ cd ∈ adjacentCells, CellCovered cd.1 cd.2 := by
  exact StableVotingDistortion.Lemma9Reduction.verifiedMassIntervals
end StableVotingDistortion.PaperMiddle

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperFamilies
noncomputable section


theorem released_lp_high_second {p q z r : ℝ} (hp : p∈Icc pA pC)
    (hq : q∈Icc (0:ℝ) p) (hz : z∈Icc p 1) (hr : r∈Icc 1 (PaperCurve.maxRatioQ:ℝ)) :
    highSecond lam PaperCurve.score (entry Knot.beta p) (-1) (entry Knot.eta p) p q z r ≤ 0 :=
  released_lp_high_second_of_cells physical_lp_cells hp hq hz hr

end
end StableVotingDistortion.PaperMiddle
end

namespace StableVotingDistortion.PaperCurve
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem canonical_second_low_q {p q z : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) PaperCurve.lam) (hz : z ∈ Icc p 1) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by
  exact StableVotingDistortion.Lemma9Reduction.verifiedCanonicalSecond hp hq hz
end StableVotingDistortion.PaperCurve

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperFamilies


theorem canonical_closed {p : ℝ} (hp : p∈Icc PaperMiddle.pC PaperMiddle.p1) :
    ReducedBoxes score .canonical .above maxRatioQ p :=
  canonical_reduced_of_grid canonical_base_all canonical_second_low_q hp

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperFamilies
open PaperCurve (score maxRatioQ)

theorem original_middle_ranges : ReducedRanges score maxRatioQ :=
  middle_ranges_from_inequalities low_first_lp_verified PaperAnalytic.released_lp_L2
    released_lp_high_second PaperCurve.canonical_closed


theorem published_lemma_9 :
    VerifierHypotheses lam score (beta score) (corr score) ∧ 1+2*lam=2.1248 :=
  ⟨(named_witness_of_middle_boxes original_middle_ranges).1,by norm_num [lam]⟩

end StableVotingDistortion.PaperMiddle
end

open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem solution : VerifierHypotheses PaperMiddle.lam score (beta score) (corr score) ∧ 1+2*PaperMiddle.lam=2.1248 := by
  exact PaperMiddle.published_lemma_9
