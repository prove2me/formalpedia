-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.firstLowCorrectionBudget
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:32:13.134935+00:00
-- url     : https://prove2.me/submissions/fffb6915-0dd0-4ec7-9b80-721ea8178b86

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
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


end
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

end StableVotingDistortion
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

end
end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperBox


structure Bounds where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

namespace Bounds
def Holds (i : Bounds) (x : ℝ) : Prop := (i.lo:ℝ) ≤ x ∧ x ≤ (i.hi:ℝ)

def point (q : ℚ) : Bounds := ⟨q,q⟩
def plus (i j : Bounds) : Bounds := ⟨i.lo+j.lo,i.hi+j.hi⟩
def neg (i : Bounds) : Bounds := ⟨-i.hi,-i.lo⟩
def minus (i j : Bounds) : Bounds := i.plus j.neg
def hull (i j : Bounds) : Bounds := ⟨min i.lo j.lo,max i.hi j.hi⟩
def meet (i j : Bounds) : Bounds := ⟨max i.lo j.lo,min i.hi j.hi⟩
def times (i j : Bounds) : Bounds :=
  ⟨min (min (i.lo*j.lo) (i.hi*j.lo)) (min (i.lo*j.hi) (i.hi*j.hi)),
   max (max (i.lo*j.lo) (i.hi*j.lo)) (max (i.lo*j.hi) (i.hi*j.hi))⟩
def reciprocal (i : Bounds) : Bounds := ⟨i.hi⁻¹,i.lo⁻¹⟩
def posPart (i : Bounds) : Bounds := ⟨max i.lo 0,max i.hi 0⟩

theorem point_holds (q : ℚ) : (point q).Holds (q:ℝ) := ⟨le_rfl,le_rfl⟩
theorem plus_holds {i j : Bounds} {x y : ℝ} (hx : i.Holds x) (hy : j.Holds y) :
    (i.plus j).Holds (x+y) := by
  simpa only [Holds, plus, Rat.cast_add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)
theorem neg_holds {i : Bounds} {x : ℝ} (hx : i.Holds x) : i.neg.Holds (-x) := by
  simpa only [Holds, neg, Rat.cast_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
theorem minus_holds {i j : Bounds} {x y : ℝ} (hx : i.Holds x) (hy : j.Holds y) :
    (i.minus j).Holds (x-y) := plus_holds hx (neg_holds hy)
theorem hull_left (i j : Bounds) {x : ℝ} (h : i.Holds x) : (i.hull j).Holds x := by
  simp only [Holds,hull,Rat.cast_min,Rat.cast_max]
  exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
theorem hull_right (i j : Bounds) {x : ℝ} (h : j.Holds x) : (i.hull j).Holds x := by
  simpa only [hull,min_comm,max_comm] using hull_left j i h
theorem meet_holds {i j : Bounds} {x : ℝ} (h : i.Holds x) (h' : j.Holds x) :
    (i.meet j).Holds x := by
  simp only [Holds,meet,Rat.cast_min,Rat.cast_max]
  exact ⟨max_le h.1 h'.1, le_min h.2 h'.2⟩

private theorem upper_mul {l u x t k : ℝ} (h : l ≤ x ∧ x ≤ u)
    (hl : l*t ≤ k) (hu : u*t ≤ k) : x*t ≤ k := by
  rcases le_total 0 t with ht|ht
  · exact (mul_le_mul_of_nonneg_right h.2 ht).trans hu
  · exact (mul_le_mul_of_nonpos_right h.1 ht).trans hl

private theorem lower_mul {l u x t k : ℝ} (h : l ≤ x ∧ x ≤ u)
    (hl : k ≤ l*t) (hu : k ≤ u*t) : k ≤ x*t := by
  rcases le_total 0 t with ht|ht
  · exact hl.trans (mul_le_mul_of_nonneg_right h.1 ht)
  · exact hu.trans (mul_le_mul_of_nonpos_right h.2 ht)

theorem times_holds {i j : Bounds} {x y : ℝ} (hx : i.Holds x) (hy : j.Holds y) :
    (i.times j).Holds (x*y) := by
  simp only [Holds,times,Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  constructor
  · rw [mul_comm x y]; apply lower_mul hy
    · rw [mul_comm (j.lo:ℝ) x]; apply lower_mul hx <;> exact (min_le_left _ _).trans (by first | apply min_le_left | apply min_le_right)
    · rw [mul_comm (j.hi:ℝ) x]; apply lower_mul hx <;> exact (min_le_right _ _).trans (by first | apply min_le_left | apply min_le_right)
  · rw [mul_comm x y]; apply upper_mul hy
    · rw [mul_comm]; apply upper_mul hx <;> exact (by first | apply le_max_left | apply le_max_right : _ ≤ max _ _) |>.trans (le_max_left _ _)
    · rw [mul_comm]; apply upper_mul hx <;> exact (by first | apply le_max_left | apply le_max_right : _ ≤ max _ _) |>.trans (le_max_right _ _)

def horner (coeff : List ℚ) (i : Bounds) : Bounds :=
  coeff.foldr (fun a acc => (point a).plus (i.times acc)) (point 0)

end Bounds
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

theorem clamp_sound {i : Bounds} {x : ℝ} (h : i.Holds x) :
    (clamp i).Holds (max 0 (min 1 x)) := by
  simp only [clamp,Holds,Rat.cast_max,Rat.cast_min,Rat.cast_zero,Rat.cast_one]
  exact ⟨max_le_max le_rfl (min_le_min le_rfl h.1),max_le_max le_rfl (min_le_min le_rfl h.2)⟩

def linearRange (col : Knot → ℕ) (k l : Knot) (i : Bounds) : Bounds :=
  let frac := clamp ((i.minus (point (abscissa k))).times (point ((abscissa l-abscissa k)⁻¹)))
  (point (ordinate col k)).plus (frac.times (point (ordinate col l-ordinate col k)))

theorem linearRange_sound (col : Knot → ℕ) (k l : Knot) {i : Bounds} {x : ℝ}
    (h : i.Holds x) : (linearRange col k l i).Holds (interpolate col k l x) := by
  have hfrac := clamp_sound (times_holds (minus_holds h (point_holds (abscissa k)))
    (point_holds ((abscissa l-abscissa k)⁻¹)))
  have hh := plus_holds (point_holds (ordinate col k))
    (times_holds hfrac (point_holds (ordinate col l-ordinate col k)))
  have he : interpolate col k l x = (ordinate col k:ℝ) +
      max 0 (min 1 ((x-(abscissa k:ℝ))*((abscissa l-abscissa k:ℚ)⁻¹:ℚ))) *
      ((ordinate col l-ordinate col k:ℚ):ℝ) := by
    simp [interpolate,fraction,ordinate,abscissa,value,rank,div_eq_mul_inv]
    <;> ring
  rw [he]; exact hh

def lookupRange (col : Knot → ℕ) (i : Bounds) (k : Knot) (ks : List Knot) : Bounds :=
  match ks with
  | [] => point (ordinate col k)
  | l::tail => if i.hi ≤ abscissa l then linearRange col k l i
    else if abscissa l < i.lo then lookupRange col i l tail
    else (linearRange col k l ⟨i.lo,abscissa l⟩).hull (lookupRange col ⟨abscissa l,i.hi⟩ l tail)

theorem lookupRange_sound (col : Knot → ℕ) (ks : List Knot) (k : Knot) (i : Bounds)
    (x : ℝ) (hx : i.Holds x) : (lookupRange col i k ks).Holds (lookup col x k ks) := by
  induction ks generalizing k i with
  | nil => simpa [lookupRange,lookup,ordinate,value] using point_holds (ordinate col k)
  | cons l tail ih =>
    have hcast : (abscissa l:ℝ) = rank l := by simp [rank,abscissa]
    by_cases h₁ : i.hi ≤ abscissa l
    · have hb : x ≤ rank l := (hx.2.trans (by exact_mod_cast h₁ : (i.hi:ℝ) ≤ abscissa l)).trans_eq hcast
      simpa [lookupRange,lookup,h₁,hb] using linearRange_sound col k l hx
    by_cases h₂ : abscissa l < i.lo
    · have ha : rank l < x := hcast.symm.trans_lt (lt_of_lt_of_le (by exact_mod_cast h₂ : (abscissa l:ℝ) < i.lo) hx.1)
      simpa [lookupRange,lookup,h₁,h₂,ha.not_ge] using ih l i hx
    rw [lookupRange,if_neg h₁,if_neg h₂]
    by_cases h : x ≤ rank l
    · rw [lookup,if_pos h]
      exact hull_left _ _ (linearRange_sound col k l ⟨hx.1,h.trans_eq hcast.symm⟩)
    · rw [lookup,if_neg h]
      exact hull_right _ _ (ih l _ ⟨hcast.le.trans (le_of_not_ge h),hx.2⟩)

def entryBox (col : Knot → ℕ) (i : Bounds) : Bounds := lookupRange col i knots.head! knots.tail

theorem entryBox_holds (col : Knot → ℕ) {i : Bounds} {x : ℝ} (h : i.Holds x) :
    (entryBox col i).Holds (entry col x) := lookupRange_sound _ _ _ _ _ h

end StableVotingDistortion.PaperMiddle
end

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
namespace StableVotingDistortion.PaperCurve
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000



def centralPiece : Piece := rows30[4]!
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
open Bounds Set


def decreasingRange (atPoint : ℚ → Bounds) (i : Bounds) : Bounds :=
  ⟨(atPoint i.hi).lo,(atPoint i.lo).hi⟩

theorem decreasingRange_sound {f : ℝ → ℝ} {atPoint : ℚ → Bounds} {l h : ℚ}
    (hm : AntitoneOn f (Icc (l:ℝ) h)) (vals : ∀ q, l ≤ q → q ≤ h → (atPoint q).Holds (f q))
    {i : Bounds} {x : ℝ} (hx : i.Holds x) (hd : x ∈ Icc (l:ℝ) h) :
    (decreasingRange atPoint (i.meet ⟨l,h⟩)).Holds (f x) := by
  let k := i.meet ⟨l,h⟩
  have hk : k.Holds x := meet_holds hx hd
  have hl : l ≤ k.lo := le_max_right _ _
  have hu : k.hi ≤ h := min_le_right _ _
  have hh : k.lo ≤ k.hi := by exact_mod_cast hk.1.trans hk.2
  have h₁ := vals k.lo hl (hh.trans hu)
  have h₂ := vals k.hi (hl.trans hh) hu
  have hlo : (k.lo:ℝ) ∈ Icc (l:ℝ) h := ⟨by exact_mod_cast hl,by exact_mod_cast hh.trans hu⟩
  have hhi : (k.hi:ℝ) ∈ Icc (l:ℝ) h := ⟨by exact_mod_cast hl.trans hh,by exact_mod_cast hu⟩
  exact ⟨h₂.1.trans (hm hd hhi hk.2),(hm hlo hd hk.1).trans h₁.2⟩


def unimodalRange (atPoint : ℚ → Bounds) (t : ℚ) (i : Bounds) : Bounds :=
  if i.hi ≤ t then ⟨(atPoint i.lo).lo,(atPoint i.hi).hi⟩
  else if t ≤ i.lo then decreasingRange atPoint i
  else ⟨min (atPoint i.lo).lo (atPoint i.hi).lo,(atPoint t).hi⟩

end StableVotingDistortion.PaperBox
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

theorem qscore_exact (x : ℚ) : (qscore x:ℝ) = score x :=
  cast_qselect _ _ Piece.cast_qvalue _ _ x
theorem qprimitive_exact (x : ℚ) : (qprimitive x:ℝ)=primitive x :=
  cast_qselect _ _ Piece.cast_qprimitive _ _ x

def scoreBox (i : Bounds) : Bounds :=
  decreasingRange (fun q => Bounds.point (qscore q)) (i.meet ⟨0,1⟩)
def primitiveBox (i : Bounds) : Bounds :=
  unimodalRange (fun q => Bounds.point (qprimitive q)) lamQ (i.meet ⟨0,1⟩)

theorem scoreBox_holds {i : Bounds} {x : ℝ} (hi : i.Holds x) (hx : x ∈ Icc 0 1) :
    (scoreBox i).Holds (score x) := by
  apply decreasingRange_sound (l:=0) (h:=1) (by simpa using score_antitone) _ hi (by simpa using hx)
  intro q _ _
  simp [Bounds.Holds,Bounds.point,qscore_exact]

end
end StableVotingDistortion.PaperCurve
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

theorem checkLine_sound (ok : Bounds → Bool) (P : ℝ → Prop)
    (leaf : ∀ i, ok i = true → ∀ x, i.Holds x → P x) (n : ℕ) :
    ∀ i, checkLine ok i n = true → ∀ x, i.Holds x → P x := by
  induction n with
  | zero => exact leaf
  | succ n ih =>
    intro i yes x hx
    by_cases enough : ok i = true
    · exact leaf i enough x hx
    simp only [checkLine,if_neg enough,Bool.and_eq_true_iff] at yes
    by_cases hb : x ≤ (((i.lo+i.hi)/2:ℚ):ℝ)
    · exact ih _ yes.1 x ⟨hx.1,hb⟩
    · exact ih _ yes.2 x ⟨le_of_not_ge hb,hx.2⟩

end StableVotingDistortion.PaperMiddle
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
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)


theorem product_chord {t a b c d : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ((1-t)*a+t*b)*((1-t)*c+t*d) ≤
    (1-t)*(a*c)+t*(b*d)+|b-a| * |d-c|/4 := by
  have hf : 0≤t*(1-t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hi : t*(1-t)≤1/4 := by nlinarith only [sq_nonneg (t-1/2)]
  have hw : -((b-a)*(d-c)) ≤ |b-a| * |d-c| := by rw [←abs_mul];exact neg_le_abs _
  have ho := mul_le_mul hw hi hf (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  linarith only [ho]


theorem value_chord {f : ℝ → ℝ} {a b p t : ℝ} {s : Bounds} (ht : t∈Icc (0:ℝ) 1)
    (hab : a≤b) (hp : p=(1-t)*a+t*b)
    (hl : Secants f a p s) (hr : Secants f p b s) :
    f p ≤ (1-t)*f a+t*f b+(b-a)*((s.hi:ℝ)-s.lo)/4 := by
  obtain ⟨u,hu,he⟩ := hl
  obtain ⟨v,hv,he'⟩ := hr
  have hw : u-v ≤ (s.hi:ℝ)-s.lo := sub_le_sub hu.2 hv.1
  have hn := sub_nonneg.mpr (hu.1.trans hu.2)
  have wt : t*(1-t)*(b-a) ≤ (b-a)/4 :=
    (mul_le_mul_of_nonneg_right (show t*(1-t)≤1/4 by nlinarith only [sq_nonneg (t-1/2)]) (sub_nonneg.mpr hab)).trans_eq (by ring)
  have non := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sub_nonneg.mpr hab)
  have ac := mul_le_mul_of_nonneg_left hw non
  have bc := mul_le_mul_of_nonneg_right wt hn
  have idn : f p - ((1-t)*f a+t*f b)=t*(1-t)*(b-a)*(u-v) := by
    rw [hp] at he he' ⊢
    linear_combination (1-t)*he - t*he'
  linarith only [idn,ac,bc]

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperCurve
open Set PaperBox PaperBox.Bounds


theorem primitive_secant {i : Bounds} {x y : ℝ} (hx : i.Holds x) (hy : i.Holds y)
    (dx : x∈Icc 0 1) (dy : y∈Icc 0 1) : Secants (J score) x y (scoreBox i) := by
  have forward {u v : ℝ} (hu : i.Holds u) (hv : i.Holds v)
      (du : u∈Icc 0 1) (dv : v∈Icc 0 1) (h : u<v) : Secants (J score) u v (scoreBox i) := by
    have hs := primitive_sandwich score_isScoreFunction du.1 h.le dv.2
    have sl := scoreBox_holds hu du
    have sr := scoreBox_holds hv dv
    have hd := sub_pos.mpr h
    let m := (J score v-J score u)/(v-u)
    refine ⟨m,⟨sr.1.trans ?_, le_trans ?_ sl.2⟩,?_⟩
    · exact (le_div_iff₀ hd).mpr (by simpa [mul_comm] using hs.1)
    · exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hs.2)
    · exact (div_mul_cancel₀ _ hd.ne').symm
  rcases lt_trichotomy x y with h|rfl|h
  · exact forward hx hy dx dy h
  · exact ⟨score x,scoreBox_holds hx dx,by simp⟩
  · obtain ⟨m,hm,he⟩ := forward hy hx dy dx h
    exact ⟨m,hm,by linear_combination -he⟩

end StableVotingDistortion.PaperCurve
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)


theorem reverse_primitive {i : Bounds} {a b : ℝ} (ha : i.Holds a) (hb : i.Holds b)
    (da : a∈Icc (0:ℝ) 1) (db : b∈Icc (0:ℝ) 1) :
    Secants (fun p => J score (1-p)) a b (PaperCurve.scoreBox ((point 1).minus i)).neg := by
  have rev {z : ℝ} (h : i.Holds z) : ((point 1).minus i).Holds (1-z) := by
    simpa using minus_holds (point_holds 1) h
  have dom {z : ℝ} (h : z∈Icc (0:ℝ) 1) : 1-z∈Icc (0:ℝ) 1 := ⟨by linarith [h.2],by linarith [h.1]⟩
  obtain ⟨s,hs,he⟩ := PaperCurve.primitive_secant (rev ha) (rev hb) (dom da) (dom db)
  exact ⟨-s,neg_holds hs,by dsimp;linear_combination he⟩


theorem mixed_bound {t β₀ β₁ J₀ J₁ Jp E₀ E₁ V y L eps : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hβ₀ : 0≤β₀) (hβ₁ : 0≤β₁) (heps : 0≤eps)
    (hj : Jp≤(1-t)*J₀+t*J₁+eps)
    (endpoints : ∀ j : Bool,
      let β := if j then β₁ else β₀
      let Jv := if j then J₁ else J₀
      let E := if j then E₁ else E₀
      β*Jv+max (E*V+y-L) 0+max β₀ β₁*eps+|β₁-β₀| * |J₁-J₀|/4 ≤ L) :
    ((1-t)*β₀+t*β₁)*Jp+max (((1-t)*E₀+t*E₁)*V+y-L) 0 ≤ L := by
  let b := (1-t)*β₀+t*β₁
  let k₀ := max (E₀*V+y-L) 0
  let k₁ := max (E₁*V+y-L) 0
  have a : 0≤1-t := sub_nonneg.mpr ht.2
  have hb : 0≤b := add_nonneg (mul_nonneg a hβ₀) (mul_nonneg ht.1 hβ₁)
  have ub : b ≤ max β₀ β₁ := by
    have z := add_le_add (mul_le_mul_of_nonneg_left (le_max_left β₀ β₁) a)
      (mul_le_mul_of_nonneg_left (le_max_right β₀ β₁) ht.1)
    dsimp [b];linarith only [z]
  have ce : max (((1-t)*E₀+t*E₁)*V+y-L) 0≤(1-t)*k₀+t*k₁ := by
    apply max_le
    · have h := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (E₀*V+y-L) 0) a)
        (mul_le_mul_of_nonneg_left (le_max_left (E₁*V+y-L) 0) ht.1)
      dsimp [k₀,k₁];linarith only [h]
    · exact add_nonneg (mul_nonneg a (le_max_right _ _)) (mul_nonneg ht.1 (le_max_right _ _))
  have w₀ := endpoints false
  have w₁ := endpoints true
  simp only [Bool.false_eq_true,if_false,if_true] at w₀ w₁
  have H := add_le_add (mul_le_mul_of_nonneg_left w₀ a) (mul_le_mul_of_nonneg_left w₁ ht.1)
  have ch := product_chord (a:=β₀) (b:=β₁) (c:=J₀) (d:=J₁) ht
  have le₁ := mul_le_mul_of_nonneg_left hj hb
  have le₂ := mul_le_mul_of_nonneg_right ub heps
  dsimp [b,k₀,k₁] at *
  linarith only [le₁, le₂, H, ch, ce]

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)

def knotArea (k : Knot) : ℚ := PaperCurve.qprimitive (1-abscissa k)
def knotPP (k : Knot) : ℚ := PaperCurve.qscore (1-abscissa k)
def chordEps (k l : Knot) : ℚ :=
  (abscissa l-abscissa k)*(knotPP l-knotPP k)/4
def chordError (k l : Knot) : ℚ :=
  max (ordinate Knot.beta k) (ordinate Knot.beta l) * chordEps k l +
  |ordinate Knot.beta l-ordinate Knot.beta k| * |knotArea l-knotArea k|/4

theorem cast_abscissa (k : Knot) : (abscissa k:ℝ) = rank k := by simp [abscissa,rank]
theorem cast_ordinate (j : Knot → ℕ) (k : Knot) : (ordinate j k:ℝ) = value j k := by simp [ordinate,value]
theorem cast_area (k : Knot) (hi : rank k∈Icc (0:ℝ) 1) :
    (knotArea k:ℝ)=J score (1-rank k) := by
  have h : 1-rank k∈Icc (0:ℝ) 1 := ⟨by linarith [hi.2],by linarith [hi.1]⟩
  rw [PaperCurve.J_score h,knotArea,PaperCurve.qprimitive_exact,Rat.cast_sub,Rat.cast_one,cast_abscissa]
theorem primitive_chord_for_knots (k l : Knot) {p t : ℝ}
    (ha : rank k∈Icc (0:ℝ) 1) (hb : rank l∈Icc (0:ℝ) 1) (hkl : rank k≤rank l)
    (ht : t∈Icc (0:ℝ) 1) (hx : p∈Icc (rank k) (rank l)) (he : p=(1-t)*rank k+t*rank l) :
    J score (1-p) ≤ (1-t)*(knotArea k:ℝ)+t*(knotArea l:ℝ)+(chordEps k l:ℝ) := by
  let b : Bounds := ⟨-knotPP l,-knotPP k⟩
  have sec (u v : ℝ) (hu : u∈Icc (rank k) (rank l)) (hv : v∈Icc (rank k) (rank l)) :
      Secants (fun s => J score (1-s)) u v b := by
    let box : Bounds := ⟨abscissa k,abscissa l⟩
    have boxmem (z : ℝ) (hz : z∈Icc (rank k) (rank l)) : box.Holds z := by
      simpa only [box,Holds,cast_abscissa,Set.mem_Icc] using hz
    have dom (z : ℝ) (hz : z∈Icc (rank k) (rank l)) : z∈Icc (0:ℝ) 1 := ⟨ha.1.trans hz.1,hz.2.trans hb.2⟩
    obtain ⟨m,hm,hm'⟩ := reverse_primitive (boxmem _ hu) (boxmem _ hv) (dom _ hu) (dom _ hv)
    have lo : (0:ℚ)≤1-abscissa l := by
      have a : (abscissa l:ℝ) ≤ 1 := (cast_abscissa l).trans_le hb.2
      exact sub_nonneg.mpr (by exact_mod_cast a)
    have hi : 1-abscissa k≤1 := by
      have a : (0:ℝ)≤(abscissa k:ℝ) := ha.1.trans_eq (cast_abscissa k).symm
      exact sub_le_self _ (by exact_mod_cast a)
    have lo' : (0:ℚ) ≤ 1 + -abscissa l := by simpa only [sub_eq_add_neg] using lo
    have hi' : 1 + -abscissa k ≤ (1:ℚ) := by simpa only [sub_eq_add_neg] using hi
    refine ⟨m,?_,hm'⟩
    simpa [box,b,PaperCurve.scoreBox,PaperBox.decreasingRange,Holds,meet,point,minus,plus,neg,knotPP,
      max_eq_left lo',min_eq_left hi',sub_eq_add_neg] using hm
  have h := value_chord ht hkl he (sec _ _ ⟨le_rfl,hkl⟩ hx) (sec _ _ hx ⟨hkl,le_rfl⟩)
  simpa only [b,chordEps,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_neg,Rat.cast_ofNat,cast_abscissa,
    cast_area k ha,cast_area l hb,neg_sub_neg] using h

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open Set PaperCurve

structure Segment where
  lo : ℚ
  hi : ℚ
  origin : ℚ
  slope : ℚ
  deriving DecidableEq,Repr
def Segment.line (s : Segment) (x : ℝ) : ℝ := s.origin+s.slope*(x-s.lo)
def Segment.qline (s : Segment) (x : ℚ) : ℚ := s.origin+s.slope*(x-s.lo)
def segmentChain (a : ℚ) : List Segment → ℚ → Prop
  | [],b => a=b
  | s::ss,b => a=s.lo ∧ s.lo ≤ s.hi ∧ segmentChain s.hi ss b
instance (a b : ℚ) (ss : List Segment) : Decidable (segmentChain a ss b) := by
  induction ss generalizing a with
  | nil => exact inferInstanceAs (Decidable (a=b))
  | cons s ss ih => letI := ih s.hi;exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem segment_cover {a b : ℚ} {ss : List Segment} (chain : segmentChain a ss b)
    {x : ℝ} (hx : x∈Icc (a:ℝ) b) (hne : ss≠[]) : ∃ s∈ss,x∈Icc (s.lo:ℝ) s.hi := by
  induction ss generalizing a with
  | nil => contradiction
  | cons s ss ih =>
    obtain ⟨rfl,_,ht⟩ := chain
    by_cases h : x ≤ s.hi
    · exact ⟨s,by simp,⟨hx.1,h⟩⟩
    have ne : ss≠[] := by
      rintro rfl
      have hb : s.hi=b := ht
      exact h (hb ▸ hx.2)
    obtain ⟨u,hu,hi⟩ := ih ht ⟨le_of_not_ge h,hx.2⟩ ne
    exact ⟨u,by simp [hu],hi⟩

def shiftStep (a : ℚ) : ℚ → List ℚ → List ℚ
  | b,[] => [b]
  | b,c::cs => (b+a*c)::shiftStep a c cs

private theorem horner_step (a b : ℚ) (cs : List ℚ) (x : ℝ) :
    horner (shiftStep a b cs) x = b+((a:ℝ)+x)*horner cs x := by
  induction cs generalizing b with
  | nil => simp [shiftStep,horner]
  | cons c cs ih =>
    change (((b+a*c:ℚ):ℝ)+x*horner (shiftStep a c cs) x) = b+((a:ℝ)+x)*((c:ℝ)+x*horner cs x)
    rw [ih];push_cast;ring

def shiftCoeffs (a : ℚ) (cs : List ℚ) : List ℚ := cs.foldr (shiftStep a) []
theorem horner_shift (a : ℚ) (cs : List ℚ) (x : ℝ) :
    horner (shiftCoeffs a cs) x=horner cs ((a:ℝ)+x) := by
  induction cs with
  | nil => rfl
  | cons b cs ih =>
    change horner (shiftStep a b (shiftCoeffs a cs)) x = (b:ℝ)+((a:ℝ)+x)*horner cs ((a:ℝ)+x)
    rw [horner_step,ih]

def difference (r : Piece) (s : Segment) : List ℚ :=
  [s.qline r.lo-r.c 0,s.slope-r.c 1,-r.c 2,-r.c 3,-r.c 4,-r.c 5,-r.c 6]

theorem horner_difference (r : Piece) (s : Segment) (x : ℝ) :
    horner (difference r s) (x-r.lo)=s.line x-r.value x := by
  simp [difference,Segment.line,Segment.qline,Piece.value,pad,horner] <;> ring

def rowOK (r : Piece) (s : Segment) : Bool :=
  let l := max s.lo r.lo
  let h := min s.hi r.hi
  if h<l then true else decide (0 ≤ lower (shiftCoeffs (l-r.lo) (difference r s)) (h-l))

theorem rowOK_sound {r : Piece} {s : Segment} (ok : rowOK r s=true)
    {x : ℝ} (hx : x∈Icc (r.lo:ℝ) r.hi) (hs : x∈Icc (s.lo:ℝ) s.hi) : r.value x ≤ s.line x := by
  let l := max s.lo r.lo
  let h := min s.hi r.hi
  have hl : (l:ℝ) ≤ x := by simpa [l] using max_le hs.1 hx.1
  have hh : x ≤ (h:ℝ) := by simpa [h] using le_min hs.2 hx.2
  have hor : l≤h := by exact_mod_cast hl.trans hh
  change (if h<l then true else decide _) = true at ok
  rw [if_neg hor.not_gt] at ok
  have cert : (0:ℝ) ≤ (lower (shiftCoeffs (l-r.lo) (difference r s)) (h-l):ℝ) := by
    exact_mod_cast of_decide_eq_true ok
  have hb := lower_le_horner (shiftCoeffs (l-r.lo) (difference r s)) (sub_nonneg.mpr hl)
    (show x-(l:ℝ)≤((h-l:ℚ):ℝ) by push_cast;linarith)
  rw [horner_shift,show ((l-r.lo:ℚ):ℝ)+(x-l)=x-r.lo by push_cast;ring,horner_difference] at hb
  linarith

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperEndpoint
open Set PaperCurve


end StableVotingDistortion.PaperEndpoint
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
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperCurve (score)
open PaperAnalytic (Segment)

def capValue (E : ℚ) (s : Segment) (x : ℚ) : ℚ :=
  E*(s.origin+s.slope*(x-s.lo))+x-PaperCurve.lamQ

def segmentCap (E : ℚ) (s : Segment) : ℚ := max (capValue E s s.lo) (capValue E s s.hi)
def maxCaps (E : ℚ) (ss : List Segment) : ℚ := ss.foldr (fun s v => max (segmentCap E s) v) 0
def sourceCap (segments : List Segment) (k : Knot) : ℚ := maxCaps (ordinate Knot.eta k) segments

private theorem maxCaps_nonneg (E : ℚ) (ss : List Segment) : 0 ≤ maxCaps E ss := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih => exact ih.trans (le_max_right _ _)
private theorem maxCaps_mem (E : ℚ) {s : Segment} {ss : List Segment} (h : s∈ss) :
    segmentCap E s ≤ maxCaps E ss := by
  induction ss with
  | nil => contradiction
  | cons v ss ih =>
    rcases List.mem_cons.mp h with rfl|ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

def Majorizes (segments : List Segment) : Prop :=
  ∀ x∈Icc (0:ℝ) PaperCurve.lam, ∃ s∈segments, x∈Icc (s.lo:ℝ) s.hi ∧ score x ≤ s.line x

theorem sourceCap_sound {segments : List Segment} (good : Majorizes segments) (k : Knot) {x : ℝ} (hx : x∈Icc (0:ℝ) PaperCurve.lam) :
    max (value Knot.eta k*score x+x-PaperCurve.lam) 0 ≤ (sourceCap segments k:ℝ) := by
  obtain ⟨s,hs,hr,hh⟩ := good x hx
  have he : 0≤value Knot.eta k := by unfold value; positivity
  have left : (capValue (ordinate Knot.eta k) s s.lo:ℝ) ≤ (sourceCap segments k:ℝ) := by
    exact_mod_cast (le_max_left _ _).trans (maxCaps_mem (ordinate Knot.eta k) hs)
  have right : (capValue (ordinate Knot.eta k) s s.hi:ℝ) ≤ (sourceCap segments k:ℝ) := by
    exact_mod_cast (le_max_right _ _).trans (maxCaps_mem (ordinate Knot.eta k) hs)
  have upper := mul_le_mul_of_nonneg_left hh he
  obtain ⟨t,ht,eq⟩ := affine_parameter hr
  have la := add_le_add (mul_le_mul_of_nonneg_left left (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left right ht.1)
  push_cast [capValue,PaperCurve.lamQ] at la
  rw [cast_ordinate] at la
  apply max_le _ (by exact_mod_cast maxCaps_nonneg (ordinate Knot.eta k) segments)
  unfold Segment.line at upper
  rw [eq] at upper ⊢
  unfold PaperCurve.lam PaperCurve.lamQ
  linarith only [la,upper]

def checkCell (segments : List Segment) (pair : Knot×Knot) : Bool :=
  let (k,l) := pair
  let err := chordError k l
  decide (abscissa k ≤ 1 ∧ abscissa l ≤ 1 ∧ 0 ≤ chordEps k l ∧
    ordinate Knot.beta k*knotArea k+sourceCap segments k+err ≤ PaperCurve.lamQ ∧
    ordinate Knot.beta l*knotArea l+sourceCap segments l+err ≤ PaperCurve.lamQ)

theorem curve_from_cells {segments : List Segment} (good : Majorizes segments)
    (cells : adjacentCells.all (checkCell segments) = true) {p x : ℝ}
    (hp : p∈Icc (3/50:ℝ) (16/25)) (hx : x∈Icc (0:ℝ) PaperCurve.lam) :
    entry Knot.beta p * J score (1-p) + max (entry Knot.eta p * score x + x - PaperCurve.lam) 0 ≤ PaperCurve.lam := by
  obtain ⟨k,l,mem,lt,hm,en⟩ := lp_cell (by simpa [pA,pC] using hp)
  have cc := List.all_eq_true.mp cells _ mem
  dsimp only [checkCell] at cc
  obtain ⟨dk,dl,ep,sk,sl⟩ := of_decide_eq_true cc
  have dom (i : Knot) (di : abscissa i ≤ 1) : rank i ∈ Icc (0:ℝ) 1 := by
    refine ⟨by unfold rank; positivity,?_⟩
    rw [←cast_abscissa];exact_mod_cast di
  obtain ⟨t,ht,eq⟩ := affine_parameter hm
  have eq' : p=(1-t)*rank k+t*rank l := by linarith only [eq]
  have jb := primitive_chord_for_knots k l (dom k dk) (dom l dl) lt.le ht hm eq'
  have interp (j : Knot → ℕ) : entry j p=(1-t)*value j k+t*value j l := by
    rw [en,interpolate_eq _ _ _ _ lt hm,eq'];field_simp [sub_ne_zero.mpr lt.ne']; ring
  have up (i : Knot) (hi : ordinate Knot.beta i*knotArea i+sourceCap segments i+chordError k l≤PaperCurve.lamQ) :
      value Knot.beta i*(knotArea i:ℝ)+max (value Knot.eta i*score x+x-PaperCurve.lam) 0+
      max (value Knot.beta k) (value Knot.beta l)*(chordEps k l:ℝ)+
      |value Knot.beta l-value Knot.beta k| * |(knotArea l:ℝ)-knotArea k|/4 ≤ PaperCurve.lam := by
    have ho : (ordinate Knot.beta i:ℝ)*(knotArea i:ℝ)+(sourceCap segments i:ℝ)+(chordError k l:ℝ)≤PaperCurve.lam := by
      unfold PaperCurve.lam; exact_mod_cast hi
    simp only [chordError,Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_max,Rat.cast_sub,Rat.cast_abs,
      Rat.cast_ofNat,cast_ordinate] at ho
    linarith only [ho,sourceCap_sound good i hx]
  have bound := mixed_bound ht (by unfold value;positivity : 0≤value Knot.beta k)
    (by unfold value;positivity : 0≤value Knot.beta l) (by exact_mod_cast ep : (0:ℝ)≤chordEps k l) jb
    (E₀:=value Knot.eta k) (E₁:=value Knot.eta l) (V:=score x) (y:=x) (L:=PaperCurve.lam)
    (by intro j;cases j with
        | false => exact up k sk
        | true => exact up l sl)
  rw [←interp,←interp] at bound
  exact bound

end StableVotingDistortion.PaperMiddle
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperAnalytic
open PaperCurve


def segments : List Segment := [
  ⟨0,(527/2000),(43784691/100000000),(-902913/1317500)⟩,
  ⟨(527/2000),(3225187/12000000),(257268003/1000000000),(-20709/315935)⟩,
  ⟨(3225187/12000000),(1644187/6000000),(51384591/200000000),(-105804/1579675)⟩,
  ⟨(1644187/6000000),(1117187/4000000),(256570393/1000000000),(-21627/315935)⟩,
  ⟨(1117187/4000000),(853687/3000000),(128105029/500000000),(-110529/1579675)⟩,
  ⟨(853687/3000000),(695587/2400000),(255841751/1000000000),(-112998/1579675)⟩,
  ⟨(695587/2400000),(590187/2000000),(997911/3906250),(-115539/1579675)⟩,
  ⟨(590187/2000000),(356784529/1200000000),(255076799/1000000000),(-1905600/2672329)⟩,
  ⟨(356784529/1200000000),(179728429/600000000),(253488759/1000000000),(-1914552/2672329)⟩,
  ⟨(179728429/600000000),(120709729/400000000),(125946629/500000000),(-1923168/2672329)⟩,
  ⟨(120709729/400000000),(91200379/300000000),(250290581/1000000000),(-1931448/2672329)⟩,
  ⟨(91200379/300000000),(73494769/240000000),(248681073/1000000000),(-1939560/2672329)⟩,
  ⟨(73494769/240000000),(61691029/200000000),(247065299/1000000000),(-1951272/2672329)⟩,
  ⟨(61691029/200000000),(372818503/1200000000),(245439243/1000000000),(-1964604/2672329)⟩,
  ⟨(372818503/1200000000),(23468177/75000000),(1523763/6250000),(-1977996/2672329)⟩,
  ⟨(23468177/75000000),(126054387/400000000),(15134611/62500000),(-1991460/2672329)⟩,
  ⟨(126054387/400000000),(38083549/120000000),(60123647/250000000),(-2006964/2672329)⟩,
  ⟨(38083549/120000000),(383507819/1200000000),(119410867/500000000),(-2023020/2672329)⟩,
  ⟨(383507819/1200000000),(32181679/100000000),(237136799/1000000000),(-2038680/2672329)⟩,
  ⟨(32181679/100000000),(388852477/1200000000),(117718939/500000000),(-2061672/2672329)⟩,
  ⟨(388852477/1200000000),(195762403/600000000),(233718113/1000000000),(-2072244/2672329)⟩,
  ⟨(195762403/600000000),(26279809/80000000),(46398241/200000000),(-188904/242939)⟩,
  ⟨(26279809/80000000),(49608683/150000000),(7195611/31250000),(-2083344/2672329)⟩,
  ⟨(49608683/150000000),(399541793/1200000000),(228523401/1000000000),(-2088420/2672329)⟩,
  ⟨(399541793/1200000000),(67035687/200000000),(226783017/1000000000),(-2093232/2672329)⟩,
  ⟨(67035687/200000000),(404886451/1200000000),(112521417/500000000),(-2106996/2672329)⟩,
  ⟨(404886451/1200000000),(20377939/60000000),(223288567/1000000000),(-2162544/2672329)⟩,
  ⟨(20377939/60000000),(136743703/400000000),(110742887/500000000),(-2217276/2672329)⟩,
  ⟨(136743703/400000000),(206451719/600000000),(13727343/62500000),(-2266200/2672329)⟩,
  ⟨(206451719/600000000),(415575767/1200000000),(217748523/1000000000),(-2310360/2672329)⟩,
  ⟨(415575767/1200000000),(4356751/12500000),(215822833/1000000000),(-2350512/2672329)⟩,
  ⟨(4356751/12500000),(703/1250),(2673249/12500000),-1⟩]

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private theorem full_cover : segmentChain 0 segments lamQ := by decide +kernel

private theorem block00 : rows00.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block01 : rows01.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block02 : rows02.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block03 : rows03.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block04 : rows04.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block05 : rows05.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block06 : rows06.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block07 : rows07.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block08 : rows08.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block09 : rows09.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block10 : rows10.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block11 : rows11.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block12 : rows12.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block13 : rows13.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block14 : rows14.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block15 : rows15.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block16 : rows16.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block17 : rows17.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block18 : rows18.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block19 : rows19.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block20 : rows20.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block21 : rows21.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block22 : rows22.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block23 : rows23.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block24 : rows24.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block25 : rows25.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block26 : rows26.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block27 : rows27.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block28 : rows28.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block29 : rows29.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block30 : rows30.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block31 : rows31.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block32 : rows32.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block33 : rows33.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block34 : rows34.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block35 : rows35.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block36 : rows36.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block37 : rows37.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block38 : rows38.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block39 : rows39.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block40 : rows40.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block41 : rows41.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block42 : rows42.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block43 : rows43.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block44 : rows44.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block45 : rows45.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block46 : rows46.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block47 : rows47.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block48 : rows48.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block49 : rows49.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel
private theorem block50 : rows50.all (fun r => segments.all (fun s => rowOK r s))=true := by decide +kernel

theorem data_majorants {r : Piece} (hr : r∈pieces) {s : Segment} (hs : s∈segments) : rowOK r s=true := by
  have join {a b : List Piece} (ha : ∀ r∈a,segments.all (rowOK r)=true) (hb : ∀ r∈b,segments.all (rowOK r)=true) :
      ∀ r∈a++b,segments.all (rowOK r)=true := by
    intro z hz;rcases List.mem_append.mp hz with h|h;exact ha z h;exact hb z h
  have H : ∀ r∈pieces,segments.all (rowOK r)=true := by
    unfold pieces;simp only [List.append_assoc]
    apply join (List.all_eq_true.mp block00)
    apply join (List.all_eq_true.mp block01)
    apply join (List.all_eq_true.mp block02)
    apply join (List.all_eq_true.mp block03)
    apply join (List.all_eq_true.mp block04)
    apply join (List.all_eq_true.mp block05)
    apply join (List.all_eq_true.mp block06)
    apply join (List.all_eq_true.mp block07)
    apply join (List.all_eq_true.mp block08)
    apply join (List.all_eq_true.mp block09)
    apply join (List.all_eq_true.mp block10)
    apply join (List.all_eq_true.mp block11)
    apply join (List.all_eq_true.mp block12)
    apply join (List.all_eq_true.mp block13)
    apply join (List.all_eq_true.mp block14)
    apply join (List.all_eq_true.mp block15)
    apply join (List.all_eq_true.mp block16)
    apply join (List.all_eq_true.mp block17)
    apply join (List.all_eq_true.mp block18)
    apply join (List.all_eq_true.mp block19)
    apply join (List.all_eq_true.mp block20)
    apply join (List.all_eq_true.mp block21)
    apply join (List.all_eq_true.mp block22)
    apply join (List.all_eq_true.mp block23)
    apply join (List.all_eq_true.mp block24)
    apply join (List.all_eq_true.mp block25)
    apply join (List.all_eq_true.mp block26)
    apply join (List.all_eq_true.mp block27)
    apply join (List.all_eq_true.mp block28)
    apply join (List.all_eq_true.mp block29)
    apply join (List.all_eq_true.mp block30)
    apply join (List.all_eq_true.mp block31)
    apply join (List.all_eq_true.mp block32)
    apply join (List.all_eq_true.mp block33)
    apply join (List.all_eq_true.mp block34)
    apply join (List.all_eq_true.mp block35)
    apply join (List.all_eq_true.mp block36)
    apply join (List.all_eq_true.mp block37)
    apply join (List.all_eq_true.mp block38)
    apply join (List.all_eq_true.mp block39)
    apply join (List.all_eq_true.mp block40)
    apply join (List.all_eq_true.mp block41)
    apply join (List.all_eq_true.mp block42)
    apply join (List.all_eq_true.mp block43)
    apply join (List.all_eq_true.mp block44)
    apply join (List.all_eq_true.mp block45)
    apply join (List.all_eq_true.mp block46)
    apply join (List.all_eq_true.mp block47)
    apply join (List.all_eq_true.mp block48)
    apply join (List.all_eq_true.mp block49)
    exact List.all_eq_true.mp block50
  exact List.all_eq_true.mp (H r hr) s hs

theorem score_majorized {x : ℝ} (hx : x∈Set.Icc (0:ℝ) lam) :
    ∃ s∈segments,x∈Set.Icc (s.lo:ℝ) s.hi ∧ score x ≤ s.line x := by
  obtain ⟨s,hs,hin⟩ := segment_cover full_cover (x:=x) (by simpa [lam] using hx) (by decide +kernel)
  obtain ⟨r,hr,hw⟩ := data_chain.exists_piece (x:=x) (by simpa [startKnot] using hx.1)
    (by simpa [endKnot] using hx.2.trans score_isScoreFunction.lam_mem.2.le) data_nonempty
  exact ⟨s,hs,hin,by rw [score_on_piece hr hw];exact rowOK_sound (data_majorants hr hs) hw hin⟩

end StableVotingDistortion.PaperAnalytic
end

section
set_option autoImplicit true
namespace StableVotingDistortion.PaperMiddle
open Set PaperBox PaperBox.Bounds
open PaperAnalytic (segments)
open PaperCurve (score)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem all_at {l : List (Knot×Knot)} {n : ℕ} (h : (l.take n).all (checkCell segments)=true)
    (t : (l.drop n).all (checkCell segments)=true) : l.all (checkCell segments)=true := by
  rw [←List.take_append_drop n l,List.all_append,h,t];rfl

private theorem batch_0 : ((adjacentCells.drop 0).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_10 : ((adjacentCells.drop 10).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_20 : ((adjacentCells.drop 20).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_30 : ((adjacentCells.drop 30).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_40 : ((adjacentCells.drop 40).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_50 : ((adjacentCells.drop 50).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_60 : ((adjacentCells.drop 60).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_70 : ((adjacentCells.drop 70).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_80 : ((adjacentCells.drop 80).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_90 : ((adjacentCells.drop 90).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_100 : ((adjacentCells.drop 100).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_110 : ((adjacentCells.drop 110).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_120 : ((adjacentCells.drop 120).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_130 : ((adjacentCells.drop 130).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_140 : ((adjacentCells.drop 140).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_150 : ((adjacentCells.drop 150).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_160 : ((adjacentCells.drop 160).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_170 : ((adjacentCells.drop 170).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_180 : ((adjacentCells.drop 180).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_190 : ((adjacentCells.drop 190).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_200 : ((adjacentCells.drop 200).take 10).all (checkCell segments)=true := by decide +kernel
private theorem batch_210 : ((adjacentCells.drop 210).take 10).all (checkCell segments)=true := by decide +kernel

private theorem complete_cell_check : adjacentCells.all (checkCell segments) = true := by
  apply all_at (n:=10) (batch_0)
  change (adjacentCells.drop 10).all (checkCell segments)=true
  apply all_at (n:=10) (batch_10)
  change (adjacentCells.drop 20).all (checkCell segments)=true
  apply all_at (n:=10) (batch_20)
  change (adjacentCells.drop 30).all (checkCell segments)=true
  apply all_at (n:=10) (batch_30)
  change (adjacentCells.drop 40).all (checkCell segments)=true
  apply all_at (n:=10) (batch_40)
  change (adjacentCells.drop 50).all (checkCell segments)=true
  apply all_at (n:=10) (batch_50)
  change (adjacentCells.drop 60).all (checkCell segments)=true
  apply all_at (n:=10) (batch_60)
  change (adjacentCells.drop 70).all (checkCell segments)=true
  apply all_at (n:=10) (batch_70)
  change (adjacentCells.drop 80).all (checkCell segments)=true
  apply all_at (n:=10) (batch_80)
  change (adjacentCells.drop 90).all (checkCell segments)=true
  apply all_at (n:=10) (batch_90)
  change (adjacentCells.drop 100).all (checkCell segments)=true
  apply all_at (n:=10) (batch_100)
  change (adjacentCells.drop 110).all (checkCell segments)=true
  apply all_at (n:=10) (batch_110)
  change (adjacentCells.drop 120).all (checkCell segments)=true
  apply all_at (n:=10) (batch_120)
  change (adjacentCells.drop 130).all (checkCell segments)=true
  apply all_at (n:=10) (batch_130)
  change (adjacentCells.drop 140).all (checkCell segments)=true
  apply all_at (n:=10) (batch_140)
  change (adjacentCells.drop 150).all (checkCell segments)=true
  apply all_at (n:=10) (batch_150)
  change (adjacentCells.drop 160).all (checkCell segments)=true
  apply all_at (n:=10) (batch_160)
  change (adjacentCells.drop 170).all (checkCell segments)=true
  apply all_at (n:=10) (batch_170)
  change (adjacentCells.drop 180).all (checkCell segments)=true
  apply all_at (n:=10) (batch_180)
  change (adjacentCells.drop 190).all (checkCell segments)=true
  apply all_at (n:=10) (batch_190)
  change (adjacentCells.drop 200).all (checkCell segments)=true
  apply all_at (n:=10) (batch_200)
  change (adjacentCells.drop 210).all (checkCell segments)=true
  apply all_at (n:=10) (batch_210)
  rfl



end StableVotingDistortion.PaperMiddle
end

open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem solution {p x : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hx : x ∈ Icc (0:ℝ) PaperCurve.lam) :
    entry PaperMiddle.Knot.beta p * J score (1-p) +
      max (entry PaperMiddle.Knot.eta p * score x + x - PaperCurve.lam) 0 ≤ PaperCurve.lam := by
  exact PaperMiddle.curve_from_cells (fun _ h => PaperAnalytic.score_majorized h) PaperMiddle.complete_cell_check hp hx
