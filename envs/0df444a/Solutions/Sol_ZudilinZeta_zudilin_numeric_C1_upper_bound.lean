-- Prove2me | solution 1 for ZudilinZeta.zudilin_numeric_C1_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T18:14:31.172233+00:00
-- url     : https://prove2.me/submissions/0b8d9f82-4306-4583-94a4-1a2223e19a1b

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13
import Theorems.Thm_ZudilinZeta_zudilin_phi_nonneg_periodic
import Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Component: PhiSweepBounds
section
namespace ZudilinZeta

noncomputable def signedStep (y : ℝ) (a : ℝ × ℤ) : ℤ :=
  if a.1<y then a.2 else if a.1=y then min a.2 0 else 0

lemma signedStep_zero_of_lt (y : ℝ) (a : ℝ × ℤ) (h : y<a.1) :
    signedStep y a=0 := by
  simp [signedStep, not_lt.mpr h.le, (ne_of_lt h).symm]

lemma signedStep_sum_lower (L : List (ℝ × ℤ))
    (hL : L.Pairwise (fun a b => a.1<b.1)) (m : ℤ)
    (hm : ∀ n : ℕ, m ≤ ((L.take n).map Prod.snd).sum) (y : ℝ) :
    m ≤ (L.map (signedStep y)).sum := by
  induction L generalizing m with
  | nil => simpa using hm 0
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.pairwise_cons.mp hL
    have h0 : m≤0 := by simpa using hm 0
    have h1 : m≤a.2 := by simpa using hm 1
    by_cases hay : a.1<y
    · have htail : m-a.2 ≤ (L.map (signedStep y)).sum := by
        apply ih hL (m-a.2)
        intro n
        have hh := hm (n+1)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at hh
        omega
      simp only [List.map_cons, List.sum_cons, signedStep, if_pos hay]
      omega
    · have hz : (L.map (signedStep y)).sum=0 := by
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
        exact signedStep_zero_of_lt y b ((le_of_not_gt hay).trans_lt (ha b hb))
      by_cases he : a.1=y
      · simpa only [List.map_cons, List.sum_cons, signedStep, if_neg hay, if_pos he,
          hz, add_zero] using (le_min h1 h0)
      · simpa only [List.map_cons, List.sum_cons, signedStep, if_neg hay, if_neg he,
          hz, add_zero] using h0

lemma floor_unit_sub (a y : ℝ) (hy0 : 0≤y) (hy1 : y<1) :
    ⌊y-a⌋ = if a-(⌊a⌋ : ℝ) ≤ y then -⌊a⌋ else -⌊a⌋-1 := by
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith [Int.floor_le a]
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith [Int.lt_floor_add_one a]

lemma floor_sub_unit (a y : ℝ) (hy0 : 0≤y) (hy1 : y<1) :
    ⌊a-y⌋ = if a-(⌊a⌋ : ℝ) < y then ⌊a⌋-1 else ⌊a⌋ := by
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith [Int.floor_le a]
  · apply Int.floor_eq_iff.mpr
    constructor <;> linarith [Int.lt_floor_add_one a]

lemma neg_floor_unit_sub_step (a y : ℝ) (hy0 : 0≤y) (hy1 : y<1)
    (d : ℤ) (hd : 0≤d) :
    -d*⌊y-a⌋ = d*⌊a⌋+d+signedStep y (a-(⌊a⌋ : ℝ), -d) := by
  rw [floor_unit_sub a y hy0 hy1]
  simp only [signedStep, min_eq_left (show -d≤0 by omega)]
  rcases lt_trichotomy (a-(⌊a⌋ : ℝ)) y with h | h | h
  · rw [if_pos h.le, if_pos h]
    ring
  · rw [if_pos h.le, if_neg (not_lt.mpr h.ge), if_pos h]
    ring
  · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h)]
    ring

lemma neg_floor_sub_unit_step (a y : ℝ) (hy0 : 0≤y) (hy1 : y<1)
    (d : ℤ) (hd : 0≤d) :
    -d*⌊a-y⌋ = -d*⌊a⌋+signedStep y (a-(⌊a⌋ : ℝ), d) := by
  rw [floor_sub_unit a y hy0 hy1]
  simp only [signedStep, min_eq_right hd]
  split_ifs <;> ring

lemma floor_sub_unit_step_lower (a y : ℝ) (hy0 : 0≤y) (hy1 : y<1)
    (d : ℤ) (hd : 0≤d) :
    d*⌊a⌋+signedStep y (a-(⌊a⌋ : ℝ), -d) ≤ d*⌊a-y⌋ := by
  rw [floor_sub_unit a y hy0 hy1]
  simp only [signedStep, min_eq_left (show -d≤0 by omega)]
  split_ifs <;> ring_nf <;> omega

end ZudilinZeta
end

-- Component: Params13PhiSweep
section
namespace ZudilinZeta

def phiSweepData : List (ℕ × ℤ) :=
  [(91,-3), (27,-3), (64,3), (29,-1), (62,1), (30,-1), (61,1),
   (31,-1), (60,1), (32,-1), (59,1), (33,-1), (58,1), (34,-1), (57,1),
   (35,-1), (56,1), (36,-1), (55,1), (37,-1), (54,1), (38,-1), (53,1)]

noncomputable def phiThreshold (x : ℝ) (a : ℕ × ℤ) : ℝ × ℤ :=
  ((a.1 : ℝ)*x-(⌊(a.1 : ℝ)*x⌋ : ℝ), a.2)

noncomputable def phiSweepBase (x : ℝ) : ℤ :=
  3*⌊91*x⌋-3*⌊27*x⌋-3*⌊64*x⌋+13+
    ∑ j ∈ Finset.Icc (29 : ℕ) 38,
      (⌊(91-2*(j : ℝ))*x⌋+⌊(j : ℝ)*x⌋-⌊(91-(j : ℝ))*x⌋)

lemma phiExpr_sweep_lower (x y : ℝ) (hy0 : 0≤y) (hy1 : y<1) :
    phiSweepBase x+((phiSweepData.map (phiThreshold x)).map (signedStep y)).sum ≤
      phiExpr params13 x y := by
  have h0 := floor_sub_unit_step_lower (91*x) y hy0 hy1 3 (by norm_num)
  have h27 := neg_floor_unit_sub_step (27*x) y hy0 hy1 3 (by norm_num)
  have h64 := neg_floor_sub_unit_step (64*x) y hy0 hy1 3 (by norm_num)
  have hu (j : ℝ) := neg_floor_unit_sub_step (j*x) y hy0 hy1 1 (by norm_num)
  have hv (j : ℝ) := neg_floor_sub_unit_step (j*x) y hy0 hy1 1 (by norm_num)
  have hy : ⌊y⌋=0 := Int.floor_eq_zero_iff.mpr ⟨hy0, hy1⟩
  norm_num [phiSweepBase, phiSweepData, phiThreshold, phiExpr, params13, eta13,
    Finset.sum_Icc_succ_top, hy]
  simp only [Int.fract] at *
  linarith only [h0, h27, h64, hu 29, hu 30, hu 31, hu 32, hu 33,
    hu 34, hu 35, hu 36, hu 37, hu 38, hv 53, hv 54, hv 55, hv 56,
    hv 57, hv 58, hv 59, hv 60, hv 61, hv 62]

lemma phi_lower_of_sweep (x : ℝ) (L : List (ℕ × ℤ)) (hp : L.Perm phiSweepData)
    (hs : (L.map (phiThreshold x)).Pairwise (fun a b => a.1<b.1)) (m : ℤ)
    (hm : ∀ n : ℕ, m ≤ phiSweepBase x+((L.take n).map Prod.snd).sum) :
    m ≤ phi params13 x := by
  apply le_csInf (show (phiExpr params13 x '' Set.Ico (0 : ℝ) 1).Nonempty from
    ⟨phiExpr params13 x 0, 0, ⟨le_rfl, zero_lt_one⟩, rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  have hs' := signedStep_sum_lower (L.map (phiThreshold x)) hs (m-phiSweepBase x)
    (fun n => by
      have hh := hm n
      simp only [← List.map_take, List.map_map, phiThreshold, Function.comp_def]
      linarith only [hh]) y
  have he := ((hp.map (phiThreshold x)).map (signedStep y)).sum_eq
  rw [he] at hs'
  have hb := phiExpr_sweep_lower x y hy.1 hy.2
  linarith only [hs', hb]

end ZudilinZeta
end

-- Component: PhiCellCertificate
section
namespace ZudilinZeta

def phiFloorSlopes : List ℕ :=
  [15,17,19,21,23,25,27,29,30,31,32,33,34,35,36,37,38,53,54,55,56,57,58,59,60,61,62,64,91]

lemma phiFloorSlopes_bounds (d : ℕ) (hd : d∈phiFloorSlopes) : 0<d ∧ d≤91 :=
  (by decide : ∀ d∈phiFloorSlopes, 0<d ∧ d≤91) d hd

lemma phiSweepData_floorSlopes (a : ℕ × ℤ) (ha : a∈phiSweepData) : a.1∈phiFloorSlopes :=
  (by decide : ∀ a∈phiSweepData, a.1∈phiFloorSlopes) a ha

def phiBaseFromFloors (f : ℕ → ℤ) : ℤ :=
  3*f 91-3*f 27-3*f 64+13+
    ∑ j ∈ Finset.Icc (29 : ℕ) 38, (f (91-2*j)+f j-f (91-j))

def phiPrefixCheck (m b : ℤ) : List (ℕ × ℤ) → Bool
  | [] => decide (m≤b)
  | a::L => decide (m≤b) && phiPrefixCheck m (b+a.2) L

lemma phiPrefixCheck_sound (m b : ℤ) (L : List (ℕ × ℤ))
    (h : phiPrefixCheck m b L=true) :
    ∀ n : ℕ, m≤b+((L.take n).map Prod.snd).sum := by
  induction L generalizing b with
  | nil => simpa [phiPrefixCheck] using h
  | cons a L ih =>
    simp only [phiPrefixCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    intro n
    cases n with
    | zero => simpa using h.1
    | succ n =>
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc]
        using ih (b+a.2) h.2 n

def phiThresholdOrderCheck (l u : ℚ) (f : ℕ → ℤ) (a b : ℕ × ℤ) : Prop :=
  (a.1<b.1 ∧ (f b.1-f a.1 : ℚ) ≤ ((b.1 : ℚ)-a.1)*l) ∨
  (b.1<a.1 ∧ ((a.1 : ℚ)-b.1)*u ≤ (f a.1-f b.1 : ℚ))

instance (l u : ℚ) (f : ℕ → ℤ) (a b : ℕ × ℤ) :
    Decidable (phiThresholdOrderCheck l u f a b) := by
  unfold phiThresholdOrderCheck
  infer_instance

lemma floor_eq_of_cell (l u : ℚ) (x : ℝ) (hl : (l : ℝ)<x) (hu : x<(u : ℝ))
    (d : ℕ) (hd : 0<d) (k : ℤ)
    (hk : (k : ℚ)≤(d : ℚ)*l ∧ (d : ℚ)*u≤(k : ℚ)+1) :
    ⌊(d : ℝ)*x⌋=k := by
  have hd' : (0 : ℝ)<d := by exact_mod_cast hd
  have hkl : (k : ℝ)≤(d : ℝ)*(l : ℝ) := by exact_mod_cast hk.1
  have hku : (d : ℝ)*(u : ℝ)≤(k : ℝ)+1 := by exact_mod_cast hk.2
  exact Int.floor_eq_iff.mpr
    ⟨hkl.trans (mul_le_mul_of_nonneg_left hl.le hd'.le),
     (mul_lt_mul_of_pos_left hu hd').trans_le hku⟩

lemma phiThresholdOrderCheck_sound (l u : ℚ) (f : ℕ → ℤ)
    (a b : ℕ × ℤ) (x : ℝ) (hl : (l : ℝ)<x) (hu : x<(u : ℝ))
    (ha : ⌊(a.1 : ℝ)*x⌋=f a.1) (hb : ⌊(b.1 : ℝ)*x⌋=f b.1)
    (h : phiThresholdOrderCheck l u f a b) :
    (phiThreshold x a).1<(phiThreshold x b).1 := by
  simp only [phiThreshold, ha, hb]
  rcases h with ⟨hab, hf⟩ | ⟨hba, hf⟩
  · have hab' : (a.1 : ℝ)<b.1 := by exact_mod_cast hab
    have hf' : (f b.1 : ℝ)-f a.1≤((b.1 : ℝ)-a.1)*(l : ℝ) := by
      exact_mod_cast hf
    have hh := mul_lt_mul_of_pos_left hl (sub_pos.mpr hab')
    nlinarith only [hf', hh]
  · have hba' : (b.1 : ℝ)<a.1 := by exact_mod_cast hba
    have hf' : ((a.1 : ℝ)-b.1)*(u : ℝ)≤(f a.1 : ℝ)-f b.1 := by
      exact_mod_cast hf
    have hh := mul_lt_mul_of_pos_left hu (sub_pos.mpr hba')
    nlinarith only [hf', hh]

lemma phiSweepData_slopes (a : ℕ × ℤ) (ha : a∈phiSweepData) :
    0<a.1 ∧ a.1≤91 := by
  simp only [phiSweepData, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

lemma phiSweepBase_eq_from_floors (x : ℝ) (f : ℕ → ℤ)
    (hf : ∀ d∈phiFloorSlopes, ⌊(d : ℝ)*x⌋=f d) :
    phiSweepBase x=phiBaseFromFloors f := by
  have h15 : ⌊15*x⌋=f 15 := hf 15 (by decide)
  have h17 : ⌊17*x⌋=f 17 := hf 17 (by decide)
  have h19 : ⌊19*x⌋=f 19 := hf 19 (by decide)
  have h21 : ⌊21*x⌋=f 21 := hf 21 (by decide)
  have h23 : ⌊23*x⌋=f 23 := hf 23 (by decide)
  have h25 : ⌊25*x⌋=f 25 := hf 25 (by decide)
  have h27 : ⌊27*x⌋=f 27 := hf 27 (by decide)
  have h29 : ⌊29*x⌋=f 29 := hf 29 (by decide)
  have h30 : ⌊30*x⌋=f 30 := hf 30 (by decide)
  have h31 : ⌊31*x⌋=f 31 := hf 31 (by decide)
  have h32 : ⌊32*x⌋=f 32 := hf 32 (by decide)
  have h33 : ⌊33*x⌋=f 33 := hf 33 (by decide)
  have h34 : ⌊34*x⌋=f 34 := hf 34 (by decide)
  have h35 : ⌊35*x⌋=f 35 := hf 35 (by decide)
  have h36 : ⌊36*x⌋=f 36 := hf 36 (by decide)
  have h37 : ⌊37*x⌋=f 37 := hf 37 (by decide)
  have h38 : ⌊38*x⌋=f 38 := hf 38 (by decide)
  have h53 : ⌊53*x⌋=f 53 := hf 53 (by decide)
  have h54 : ⌊54*x⌋=f 54 := hf 54 (by decide)
  have h55 : ⌊55*x⌋=f 55 := hf 55 (by decide)
  have h56 : ⌊56*x⌋=f 56 := hf 56 (by decide)
  have h57 : ⌊57*x⌋=f 57 := hf 57 (by decide)
  have h58 : ⌊58*x⌋=f 58 := hf 58 (by decide)
  have h59 : ⌊59*x⌋=f 59 := hf 59 (by decide)
  have h60 : ⌊60*x⌋=f 60 := hf 60 (by decide)
  have h61 : ⌊61*x⌋=f 61 := hf 61 (by decide)
  have h62 : ⌊62*x⌋=f 62 := hf 62 (by decide)
  have h64 : ⌊64*x⌋=f 64 := hf 64 (by decide)
  have h91 : ⌊91*x⌋=f 91 := hf 91 (by decide)
  norm_num [phiSweepBase, phiBaseFromFloors, Finset.sum_Icc_succ_top,
    h15, h17, h19, h21, h23, h25, h27, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h64, h91]

lemma phi_lower_of_cell (l u : ℚ) (f : ℕ → ℤ) (L : List (ℕ × ℤ)) (m : ℤ)
    (hp : L.Perm phiSweepData)
    (hf : ∀ d∈phiFloorSlopes,
      (f d : ℚ)≤(d : ℚ)*l ∧ (d : ℚ)*u≤(f d : ℚ)+1)
    (hs : L.IsChain (phiThresholdOrderCheck l u f))
    (hm : phiPrefixCheck m (phiBaseFromFloors f) L=true)
    (x : ℝ) (hl : (l : ℝ)<x) (hu : x<(u : ℝ)) :
    m≤phi params13 x := by
  have hfloor (d : ℕ) (hd : d∈phiFloorSlopes) : ⌊(d : ℝ)*x⌋=f d :=
    floor_eq_of_cell l u x hl hu d (phiFloorSlopes_bounds d hd).1 (f d) (hf d hd)
  apply phi_lower_of_sweep x L hp
  · apply List.pairwise_map.mpr
    apply List.isChain_iff_pairwise.mp
    apply hs.imp_of_mem_imp
    intro a b ha hb hab
    have ha' := phiSweepData_floorSlopes a (hp.mem_iff.mp ha)
    have hb' := phiSweepData_floorSlopes b (hp.mem_iff.mp hb)
    exact phiThresholdOrderCheck_sound l u f a b x hl hu
      (hfloor a.1 ha') (hfloor b.1 hb') hab
  · rw [phiSweepBase_eq_from_floors x f hfloor]
    exact phiPrefixCheck_sound m (phiBaseFromFloors f) L hm

def phiCellMidFloor (l u : ℚ) (d : ℕ) : ℤ := ⌊(d : ℚ)*((l+u)/2)⌋

def phiCellCheck (l u : ℚ) (L : List (ℕ × ℤ)) (m : ℤ) : Bool :=
  let f := phiCellMidFloor l u
  decide (L.Perm phiSweepData) &&
    (List.range 91).all (fun i =>
      decide ((f (i+1) : ℚ)≤((i+1 : ℕ) : ℚ)*l ∧
        ((i+1 : ℕ) : ℚ)*u≤(f (i+1) : ℚ)+1)) &&
    decide (L.IsChain (phiThresholdOrderCheck l u f)) &&
    phiPrefixCheck m (phiBaseFromFloors f) L

lemma phiCellCheck_sound (l u : ℚ) (L : List (ℕ × ℤ)) (m : ℤ)
    (h : phiCellCheck l u L m=true) (x : ℝ) (hl : (l : ℝ)<x) (hu : x<(u : ℝ)) :
    m≤phi params13 x := by
  simp only [phiCellCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine phi_lower_of_cell l u (phiCellMidFloor l u) L m h.1.1.1 ?_ h.1.2 h.2 x hl hu
  intro d hd
  have hd' := phiFloorSlopes_bounds d hd
  have hmem : d-1∈List.range 91 := List.mem_range.mpr (by omega)
  simpa only [Nat.sub_add_cancel hd'.1, decide_eq_true_eq] using h.1.1.2 (d-1) hmem

end ZudilinZeta
end

-- Component: PhiFastCellCertificate
section
namespace ZudilinZeta

structure PhiRationalCell where
  lowerNum : ℕ
  lowerDen : ℕ
  upperNum : ℕ
  upperDen : ℕ
  order : List (ℕ × ℤ)
  value : ℤ

def PhiRationalCell.lower (c : PhiRationalCell) : ℚ := c.lowerNum/c.lowerDen
def PhiRationalCell.upper (c : PhiRationalCell) : ℚ := c.upperNum/c.upperDen

def PhiRationalCell.floorValues (c : PhiRationalCell) (d : ℕ) : ℤ :=
  (d*(c.lowerNum*c.upperDen+c.upperNum*c.lowerDen) /
    (2*c.lowerDen*c.upperDen) : ℕ)

def phiIntOrderCheck (ln ld un ud : ℕ) (f : ℕ → ℤ) (a b : ℕ × ℤ) : Prop :=
  (a.1<b.1 ∧ (f b.1-f a.1)*(ld : ℤ)≤((b.1 : ℤ)-a.1)*ln) ∨
  (b.1<a.1 ∧ ((a.1 : ℤ)-b.1)*un≤(f a.1-f b.1)*(ud : ℤ))

instance (ln ld un ud : ℕ) (f : ℕ → ℤ) (a b : ℕ × ℤ) :
    Decidable (phiIntOrderCheck ln ld un ud f a b) := by
  unfold phiIntOrderCheck
  infer_instance

def PhiRationalCell.check (c : PhiRationalCell) : Bool :=
  let f := c.floorValues
  decide (0<c.lowerDen ∧ 0<c.upperDen) &&
    decide (c.order.Perm phiSweepData) &&
    phiFloorSlopes.all (fun d =>
      decide (f d*(c.lowerDen : ℤ)≤(d : ℤ)*c.lowerNum ∧
        (d : ℤ)*c.upperNum≤(f d+1)*(c.upperDen : ℤ))) &&
    decide (c.order.IsChain (phiIntOrderCheck c.lowerNum c.lowerDen
      c.upperNum c.upperDen f)) &&
    phiPrefixCheck c.value (phiBaseFromFloors f) c.order

lemma phiIntOrderCheck_sound (ln ld un ud : ℕ) (f : ℕ → ℤ) (a b : ℕ × ℤ)
    (hld : 0<ld) (hud : 0<ud) (h : phiIntOrderCheck ln ld un ud f a b) :
    phiThresholdOrderCheck ((ln : ℚ)/ld) ((un : ℚ)/ud) f a b := by
  have hld' : (0 : ℚ)<ld := by exact_mod_cast hld
  have hud' : (0 : ℚ)<ud := by exact_mod_cast hud
  rcases h with ⟨hab, hf⟩ | ⟨hba, hf⟩
  · refine Or.inl ⟨hab, ?_⟩
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hld').mpr
    exact_mod_cast hf
  · refine Or.inr ⟨hba, ?_⟩
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hud').mpr
    exact_mod_cast hf

lemma PhiRationalCell.check_sound (c : PhiRationalCell) (h : c.check=true)
    (x : ℝ) (hl : (c.lower : ℝ)<x) (hu : x<(c.upper : ℝ)) :
    c.value≤phi params13 x := by
  simp only [PhiRationalCell.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hden, hp⟩, hf⟩, hs⟩, hm⟩ := h
  have hld : (0 : ℚ)<c.lowerDen := by exact_mod_cast hden.1
  have hud : (0 : ℚ)<c.upperDen := by exact_mod_cast hden.2
  refine phi_lower_of_cell c.lower c.upper c.floorValues c.order c.value hp ?_ ?_ hm x hl hu
  · intro d hd
    have hf' := hf d hd
    constructor
    · unfold PhiRationalCell.lower
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hld).mpr
      exact_mod_cast hf'.1
    · unfold PhiRationalCell.upper
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hud).mpr
      exact_mod_cast hf'.2
  · exact hs.imp (fun a b hab => phiIntOrderCheck_sound _ _ _ _ _ a b hden.1 hden.2 hab)

end ZudilinZeta
end

-- Component: PhiCellCover
section
open MeasureTheory

namespace ZudilinZeta

def phiCellCoverCheck (l u : ℚ) (m : ℤ) : List PhiRationalCell → Bool
  | [] => decide (l=u)
  | c::L => decide (c.lower=l ∧ m≤c.value) && c.check && phiCellCoverCheck c.upper u m L

lemma phiCellCoverCheck_sound (l u : ℚ) (m : ℤ) (L : List PhiRationalCell)
    (h : phiCellCoverCheck l u m L=true) :
    ∀ᵐ x : ℝ, (l : ℝ)<x → x<(u : ℝ) → m≤phi params13 x := by
  induction L generalizing l with
  | nil =>
    have he : l=u := by simpa only [phiCellCoverCheck, decide_eq_true_eq] using h
    exact Filter.Eventually.of_forall (fun x hx hy => False.elim (by simpa [he] using hx.trans hy))
  | cons c L ih =>
    simp only [phiCellCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    filter_upwards [ih c.upper h.2, volume.ae_ne (c.upper : ℝ)] with x hx hne
    intro hl hu
    by_cases hxu : x<(c.upper : ℝ)
    · apply h.1.1.2.trans (c.check_sound h.1.2 x ?_ hxu)
      simpa only [h.1.1.1] using hl
    · exact hx (lt_of_le_of_ne (le_of_not_gt hxu) (Ne.symm hne)) hu

structure PhiCertifiedSegment where
  lower : ℚ
  upper : ℚ
  value : ℤ
  cells : List PhiRationalCell

def PhiCertifiedSegment.check (s : PhiCertifiedSegment) : Bool :=
  phiCellCoverCheck s.lower s.upper s.value s.cells

lemma PhiCertifiedSegment.check_sound (s : PhiCertifiedSegment) (hs : s.check=true) :
    ∀ᵐ x : ℝ, (s.lower : ℝ)<x → x<(s.upper : ℝ) → s.value≤phi params13 x :=
  phiCellCoverCheck_sound s.lower s.upper s.value s.cells hs

end ZudilinZeta
end

-- Component: Params13PhiCertificates
section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ZudilinZeta

def phiCertifiedSegment1 : PhiCertifiedSegment :=
  ⟨(2/91), (1/38), 3, [
    ⟨2, 91, 1, 38, [(91,-3), (53,1), (54,1), (55,1), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1)], 3⟩]⟩

lemma phiCertifiedSegment1_checked : phiCertifiedSegment1.check=true := by decide +kernel

def phiCertifiedSegment2 : PhiCertifiedSegment :=
  ⟨(1/38), (1/37), 4, [
    ⟨1, 38, 1, 37, [(38,-1), (53,1), (91,-3), (54,1), (55,1), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1), (36,-1), (37,-1)], 4⟩]⟩

lemma phiCertifiedSegment2_checked : phiCertifiedSegment2.check=true := by decide +kernel

def phiCertifiedSegment3 : PhiCertifiedSegment :=
  ⟨(1/37), (1/36), 5, [
    ⟨1, 37, 1, 36, [(37,-1), (38,-1), (53,1), (54,1), (91,-3), (55,1), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1), (36,-1)], 5⟩]⟩

lemma phiCertifiedSegment3_checked : phiCertifiedSegment3.check=true := by decide +kernel

def phiCertifiedSegment4 : PhiCertifiedSegment :=
  ⟨(1/36), (1/33), 6, [
    ⟨1, 36, 1, 35, [(36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (91,-3), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1)], 6⟩,
    ⟨1, 35, 1, 34, [(35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (91,-3), (57,1), (58,1), (59,1), (60,1), (61,1), (27,-3), (62,1), (29,-1), (64,3), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1)], 6⟩,
    ⟨1, 34, 1, 33, [(34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (91,-3), (58,1), (59,1), (60,1), (27,-3), (61,1), (62,1), (29,-1), (30,-1), (64,3), (31,-1), (32,-1), (33,-1)], 6⟩]⟩

lemma phiCertifiedSegment4_checked : phiCertifiedSegment4.check=true := by decide +kernel

def phiCertifiedSegment5 : PhiCertifiedSegment :=
  ⟨(1/33), (1/31), 7, [
    ⟨1, 33, 1, 32, [(33,-1), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (58,1), (91,-3), (59,1), (27,-3), (60,1), (61,1), (29,-1), (62,1), (30,-1), (31,-1), (64,3), (32,-1)], 7⟩,
    ⟨1, 32, 1, 31, [(32,-1), (64,3), (33,-1), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (58,1), (27,-3), (59,1), (91,-3), (60,1), (29,-1), (61,1), (30,-1), (62,1), (31,-1)], 7⟩]⟩

lemma phiCertifiedSegment5_checked : phiCertifiedSegment5.check=true := by decide +kernel

def phiCertifiedSegment6 : PhiCertifiedSegment :=
  ⟨(1/31), (1/29), 8, [
    ⟨1, 31, 2, 61, [(31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (91,-3), (30,-1), (61,1)], 8⟩,
    ⟨2, 61, 3, 91, [(61,1), (31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (30,-1), (91,-3)], 8⟩,
    ⟨3, 91, 1, 30, [(91,-3), (61,1), (31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (30,-1)], 8⟩,
    ⟨1, 30, 2, 59, [(30,-1), (60,1), (31,-1), (61,1), (91,-3), (32,-1), (62,1), (33,-1), (34,-1), (64,3), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (27,-3), (57,1), (58,1), (29,-1), (59,1)], 8⟩,
    ⟨2, 59, 1, 29, [(59,1), (30,-1), (60,1), (31,-1), (61,1), (32,-1), (91,-3), (62,1), (33,-1), (34,-1), (64,3), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (27,-3), (57,1), (58,1), (29,-1)], 8⟩]⟩

lemma phiCertifiedSegment6_checked : phiCertifiedSegment6.check=true := by decide +kernel

def phiCertifiedSegment7 : PhiCertifiedSegment :=
  ⟨(1/29), (1/28), 9, [
    ⟨1, 29, 2, 57, [(29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (91,-3), (34,-1), (35,-1), (64,3), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (27,-3), (56,1), (57,1)], 9⟩,
    ⟨2, 57, 1, 28, [(57,1), (29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (34,-1), (91,-3), (35,-1), (64,3), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (27,-3), (56,1)], 9⟩]⟩

lemma phiCertifiedSegment7_checked : phiCertifiedSegment7.check=true := by decide +kernel

def phiCertifiedSegment8 : PhiCertifiedSegment :=
  ⟨(1/28), (1/27), 8, [
    ⟨1, 28, 2, 55, [(56,1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (35,-1), (91,-3), (36,-1), (64,3), (37,-1), (38,-1), (53,1), (54,1), (27,-3), (55,1)], 8⟩,
    ⟨2, 55, 1, 27, [(55,1), (56,1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (35,-1), (36,-1), (91,-3), (64,3), (37,-1), (38,-1), (53,1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment8_checked : phiCertifiedSegment8.check=true := by decide +kernel

def phiCertifiedSegment9 : PhiCertifiedSegment :=
  ⟨(1/27), (1/25), 4, [
    ⟨1, 27, 2, 53, [(27,-3), (54,1), (55,1), (29,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (62,1), (36,-1), (37,-1), (64,3), (91,-3), (38,-1), (53,1)], 4⟩,
    ⟨2, 53, 1, 26, [(53,1), (27,-3), (54,1), (55,1), (29,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (62,1), (36,-1), (37,-1), (64,3), (38,-1), (91,-3)], 4⟩,
    ⟨1, 26, 1, 25, [(27,-3), (53,1), (54,1), (29,-1), (55,1), (30,-1), (56,1), (31,-1), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1), (60,1), (35,-1), (61,1), (36,-1), (62,1), (37,-1), (38,-1), (64,3), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment9_checked : phiCertifiedSegment9.check=true := by decide +kernel

def phiCertifiedSegment10 : PhiCertifiedSegment :=
  ⟨(1/25), (1/24), 5, [
    ⟨1, 25, 1, 24, [(27,-3), (53,1), (29,-1), (54,1), (30,-1), (55,1), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (58,1), (34,-1), (59,1), (35,-1), (60,1), (36,-1), (61,1), (37,-1), (62,1), (38,-1), (64,3), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment10_checked : phiCertifiedSegment10.check=true := by decide +kernel

def phiCertifiedSegment11 : PhiCertifiedSegment :=
  ⟨(1/24), (1/22), 4, [
    ⟨1, 24, 1, 23, [(27,-3), (29,-1), (53,1), (30,-1), (54,1), (31,-1), (55,1), (32,-1), (56,1), (33,-1), (57,1), (34,-1), (58,1), (35,-1), (59,1), (36,-1), (60,1), (37,-1), (61,1), (38,-1), (62,1), (64,3), (91,-3)], 4⟩,
    ⟨1, 23, 4, 91, [(27,-3), (29,-1), (30,-1), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1), (34,-1), (57,1), (35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (61,1), (62,1), (64,3), (91,-3)], 4⟩,
    ⟨4, 91, 1, 22, [(91,-3), (27,-3), (29,-1), (30,-1), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1), (34,-1), (57,1), (35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (61,1), (62,1), (64,3)], 4⟩]⟩

lemma phiCertifiedSegment11_checked : phiCertifiedSegment11.check=true := by decide +kernel

def phiCertifiedSegment12 : PhiCertifiedSegment :=
  ⟨(1/22), (1/20), 3, [
    ⟨1, 22, 3, 64, [(91,-3), (27,-3), (29,-1), (30,-1), (31,-1), (53,1), (32,-1), (54,1), (33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (37,-1), (59,1), (38,-1), (60,1), (61,1), (62,1), (64,3)], 3⟩,
    ⟨3, 64, 1, 21, [(64,3), (27,-3), (91,-3), (29,-1), (30,-1), (31,-1), (53,1), (32,-1), (54,1), (33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (37,-1), (59,1), (38,-1), (60,1), (61,1), (62,1)], 3⟩,
    ⟨1, 21, 3, 62, [(64,3), (27,-3), (91,-3), (29,-1), (30,-1), (31,-1), (32,-1), (53,1), (33,-1), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (58,1), (38,-1), (59,1), (60,1), (61,1), (62,1)], 3⟩,
    ⟨3, 62, 3, 61, [(62,1), (64,3), (27,-3), (29,-1), (91,-3), (30,-1), (31,-1), (32,-1), (53,1), (33,-1), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (58,1), (38,-1), (59,1), (60,1), (61,1)], 3⟩,
    ⟨3, 61, 1, 20, [(61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (91,-3), (31,-1), (32,-1), (53,1), (33,-1), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (58,1), (38,-1), (59,1), (60,1)], 3⟩]⟩

lemma phiCertifiedSegment12_checked : phiCertifiedSegment12.check=true := by decide +kernel

def phiCertifiedSegment13 : PhiCertifiedSegment :=
  ⟨(1/20), (5/91), 2, [
    ⟨1, 20, 3, 59, [(60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (91,-3), (32,-1), (33,-1), (53,1), (34,-1), (54,1), (35,-1), (55,1), (36,-1), (56,1), (37,-1), (57,1), (38,-1), (58,1), (59,1)], 2⟩,
    ⟨3, 59, 3, 58, [(59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (91,-3), (33,-1), (53,1), (34,-1), (54,1), (35,-1), (55,1), (36,-1), (56,1), (37,-1), (57,1), (38,-1), (58,1)], 2⟩,
    ⟨3, 58, 1, 19, [(58,1), (59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (91,-3), (53,1), (34,-1), (54,1), (35,-1), (55,1), (36,-1), (56,1), (37,-1), (57,1), (38,-1)], 2⟩,
    ⟨1, 19, 3, 56, [(38,-1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (53,1), (91,-3), (35,-1), (54,1), (36,-1), (55,1), (37,-1), (56,1)], 2⟩,
    ⟨3, 56, 2, 37, [(56,1), (38,-1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (64,3), (27,-3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (53,1), (35,-1), (91,-3), (54,1), (36,-1), (55,1), (37,-1)], 2⟩,
    ⟨2, 37, 3, 55, [(37,-1), (56,1), (38,-1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (53,1), (35,-1), (54,1), (91,-3), (36,-1), (55,1)], 2⟩,
    ⟨3, 55, 5, 91, [(55,1), (37,-1), (56,1), (38,-1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (53,1), (35,-1), (54,1), (36,-1), (91,-3)], 2⟩]⟩

lemma phiCertifiedSegment13_checked : phiCertifiedSegment13.check=true := by decide +kernel

def phiCertifiedSegment14 : PhiCertifiedSegment :=
  ⟨(5/91), (1/18), 5, [
    ⟨5, 91, 1, 18, [(91,-3), (55,1), (37,-1), (56,1), (38,-1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (53,1), (35,-1), (54,1), (36,-1)], 5⟩]⟩

lemma phiCertifiedSegment14_checked : phiCertifiedSegment14.check=true := by decide +kernel

def phiCertifiedSegment15 : PhiCertifiedSegment :=
  ⟨(1/18), (2/35), 4, [
    ⟨1, 18, 3, 53, [(36,-1), (54,1), (37,-1), (55,1), (91,-3), (38,-1), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1), (53,1)], 4⟩,
    ⟨3, 53, 2, 35, [(53,1), (36,-1), (54,1), (37,-1), (55,1), (38,-1), (91,-3), (56,1), (57,1), (58,1), (59,1), (60,1), (61,1), (62,1), (27,-3), (64,3), (29,-1), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1), (35,-1)], 4⟩]⟩

lemma phiCertifiedSegment15_checked : phiCertifiedSegment15.check=true := by decide +kernel

def phiCertifiedSegment16 : PhiCertifiedSegment :=
  ⟨(2/35), (1/17), 5, [
    ⟨2, 35, 1, 17, [(35,-1), (53,1), (36,-1), (54,1), (37,-1), (55,1), (38,-1), (56,1), (91,-3), (57,1), (58,1), (59,1), (60,1), (61,1), (27,-3), (62,1), (29,-1), (64,3), (30,-1), (31,-1), (32,-1), (33,-1), (34,-1)], 5⟩]⟩

lemma phiCertifiedSegment16_checked : phiCertifiedSegment16.check=true := by decide +kernel

def phiCertifiedSegment17 : PhiCertifiedSegment :=
  ⟨(1/17), (6/91), 7, [
    ⟨1, 17, 2, 33, [(34,-1), (35,-1), (36,-1), (53,1), (37,-1), (54,1), (38,-1), (55,1), (56,1), (57,1), (91,-3), (58,1), (59,1), (60,1), (27,-3), (61,1), (62,1), (29,-1), (30,-1), (64,3), (31,-1), (32,-1), (33,-1)], 7⟩,
    ⟨2, 33, 1, 16, [(33,-1), (34,-1), (35,-1), (36,-1), (53,1), (37,-1), (54,1), (38,-1), (55,1), (56,1), (57,1), (58,1), (91,-3), (59,1), (27,-3), (60,1), (61,1), (29,-1), (62,1), (30,-1), (31,-1), (64,3), (32,-1)], 7⟩,
    ⟨1, 16, 2, 31, [(32,-1), (64,3), (33,-1), (34,-1), (35,-1), (36,-1), (37,-1), (53,1), (38,-1), (54,1), (55,1), (56,1), (57,1), (58,1), (27,-3), (59,1), (91,-3), (60,1), (29,-1), (61,1), (30,-1), (62,1), (31,-1)], 7⟩,
    ⟨2, 31, 4, 61, [(31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (53,1), (38,-1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (91,-3), (30,-1), (61,1)], 7⟩,
    ⟨4, 61, 6, 91, [(61,1), (31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (53,1), (38,-1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (30,-1), (91,-3)], 7⟩]⟩

lemma phiCertifiedSegment17_checked : phiCertifiedSegment17.check=true := by decide +kernel

def phiCertifiedSegment18 : PhiCertifiedSegment :=
  ⟨(6/91), (2/29), 8, [
    ⟨6, 91, 1, 15, [(91,-3), (61,1), (31,-1), (62,1), (32,-1), (33,-1), (64,3), (34,-1), (35,-1), (36,-1), (37,-1), (53,1), (38,-1), (54,1), (55,1), (56,1), (57,1), (27,-3), (58,1), (59,1), (29,-1), (60,1), (30,-1)], 8⟩,
    ⟨1, 15, 4, 59, [(30,-1), (60,1), (31,-1), (61,1), (91,-3), (32,-1), (62,1), (33,-1), (34,-1), (64,3), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (27,-3), (57,1), (58,1), (29,-1), (59,1)], 8⟩,
    ⟨4, 59, 2, 29, [(59,1), (30,-1), (60,1), (31,-1), (61,1), (32,-1), (91,-3), (62,1), (33,-1), (34,-1), (64,3), (35,-1), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (56,1), (27,-3), (57,1), (58,1), (29,-1)], 8⟩]⟩

lemma phiCertifiedSegment18_checked : phiCertifiedSegment18.check=true := by decide +kernel

def phiCertifiedSegment19 : PhiCertifiedSegment :=
  ⟨(2/29), (1/14), 9, [
    ⟨2, 29, 4, 57, [(29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (91,-3), (34,-1), (35,-1), (64,3), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (27,-3), (56,1), (57,1)], 9⟩,
    ⟨4, 57, 1, 14, [(57,1), (29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (34,-1), (91,-3), (35,-1), (64,3), (36,-1), (37,-1), (38,-1), (53,1), (54,1), (55,1), (27,-3), (56,1)], 9⟩]⟩

lemma phiCertifiedSegment19_checked : phiCertifiedSegment19.check=true := by decide +kernel

def phiCertifiedSegment20 : PhiCertifiedSegment :=
  ⟨(1/14), (2/27), 8, [
    ⟨1, 14, 4, 55, [(56,1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (35,-1), (91,-3), (36,-1), (64,3), (37,-1), (38,-1), (53,1), (54,1), (27,-3), (55,1)], 8⟩,
    ⟨4, 55, 2, 27, [(55,1), (56,1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (35,-1), (36,-1), (91,-3), (64,3), (37,-1), (38,-1), (53,1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment20_checked : phiCertifiedSegment20.check=true := by decide +kernel

def phiCertifiedSegment21 : PhiCertifiedSegment :=
  ⟨(2/27), (3/38), 4, [
    ⟨2, 27, 4, 53, [(27,-3), (54,1), (55,1), (29,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (62,1), (36,-1), (37,-1), (64,3), (91,-3), (38,-1), (53,1)], 4⟩,
    ⟨4, 53, 1, 13, [(53,1), (27,-3), (54,1), (55,1), (29,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (62,1), (36,-1), (37,-1), (64,3), (38,-1), (91,-3)], 4⟩,
    ⟨1, 13, 5, 64, [(91,-3), (27,-3), (53,1), (54,1), (29,-1), (55,1), (30,-1), (56,1), (31,-1), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1), (60,1), (35,-1), (61,1), (36,-1), (62,1), (37,-1), (38,-1), (64,3)], 4⟩,
    ⟨5, 64, 3, 38, [(64,3), (27,-3), (91,-3), (53,1), (54,1), (29,-1), (55,1), (30,-1), (56,1), (31,-1), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1), (60,1), (35,-1), (61,1), (36,-1), (62,1), (37,-1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment21_checked : phiCertifiedSegment21.check=true := by decide +kernel

def phiCertifiedSegment22 : PhiCertifiedSegment :=
  ⟨(3/38), (1/12), 5, [
    ⟨3, 38, 2, 25, [(38,-1), (64,3), (27,-3), (53,1), (91,-3), (54,1), (29,-1), (55,1), (30,-1), (56,1), (31,-1), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1), (60,1), (35,-1), (61,1), (36,-1), (62,1), (37,-1)], 5⟩,
    ⟨2, 25, 5, 62, [(38,-1), (64,3), (27,-3), (53,1), (91,-3), (29,-1), (54,1), (30,-1), (55,1), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (58,1), (34,-1), (59,1), (35,-1), (60,1), (36,-1), (61,1), (37,-1), (62,1)], 5⟩,
    ⟨5, 62, 3, 37, [(62,1), (38,-1), (64,3), (27,-3), (53,1), (29,-1), (91,-3), (54,1), (30,-1), (55,1), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (58,1), (34,-1), (59,1), (35,-1), (60,1), (36,-1), (61,1), (37,-1)], 5⟩,
    ⟨3, 37, 5, 61, [(37,-1), (62,1), (38,-1), (27,-3), (64,3), (53,1), (29,-1), (54,1), (91,-3), (30,-1), (55,1), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (58,1), (34,-1), (59,1), (35,-1), (60,1), (36,-1), (61,1)], 5⟩,
    ⟨5, 61, 1, 12, [(61,1), (37,-1), (62,1), (38,-1), (27,-3), (64,3), (53,1), (29,-1), (54,1), (30,-1), (91,-3), (55,1), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (58,1), (34,-1), (59,1), (35,-1), (60,1), (36,-1)], 5⟩]⟩

lemma phiCertifiedSegment22_checked : phiCertifiedSegment22.check=true := by decide +kernel

def phiCertifiedSegment23 : PhiCertifiedSegment :=
  ⟨(1/12), (8/91), 4, [
    ⟨1, 12, 5, 59, [(36,-1), (60,1), (37,-1), (61,1), (38,-1), (62,1), (27,-3), (64,3), (29,-1), (53,1), (30,-1), (54,1), (31,-1), (55,1), (91,-3), (32,-1), (56,1), (33,-1), (57,1), (34,-1), (58,1), (35,-1), (59,1)], 4⟩,
    ⟨5, 59, 3, 35, [(59,1), (36,-1), (60,1), (37,-1), (61,1), (38,-1), (62,1), (27,-3), (64,3), (29,-1), (53,1), (30,-1), (54,1), (31,-1), (55,1), (32,-1), (91,-3), (56,1), (33,-1), (57,1), (34,-1), (58,1), (35,-1)], 4⟩,
    ⟨3, 35, 5, 58, [(35,-1), (59,1), (36,-1), (60,1), (37,-1), (61,1), (38,-1), (27,-3), (62,1), (29,-1), (64,3), (53,1), (30,-1), (54,1), (31,-1), (55,1), (32,-1), (56,1), (91,-3), (33,-1), (57,1), (34,-1), (58,1)], 4⟩,
    ⟨5, 58, 2, 23, [(58,1), (35,-1), (59,1), (36,-1), (60,1), (37,-1), (61,1), (38,-1), (27,-3), (62,1), (29,-1), (64,3), (53,1), (30,-1), (54,1), (31,-1), (55,1), (32,-1), (56,1), (33,-1), (91,-3), (57,1), (34,-1)], 4⟩,
    ⟨2, 23, 5, 57, [(35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (61,1), (27,-3), (62,1), (29,-1), (64,3), (30,-1), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1), (91,-3), (34,-1), (57,1)], 4⟩,
    ⟨5, 57, 8, 91, [(57,1), (35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (61,1), (27,-3), (62,1), (29,-1), (64,3), (30,-1), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1), (34,-1), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment23_checked : phiCertifiedSegment23.check=true := by decide +kernel

def phiCertifiedSegment24 : PhiCertifiedSegment :=
  ⟨(8/91), (3/34), 5, [
    ⟨8, 91, 3, 34, [(91,-3), (57,1), (35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (61,1), (27,-3), (62,1), (29,-1), (64,3), (30,-1), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1), (34,-1)], 5⟩]⟩

lemma phiCertifiedSegment24_checked : phiCertifiedSegment24.check=true := by decide +kernel

def phiCertifiedSegment25 : PhiCertifiedSegment :=
  ⟨(3/34), (2/21), 4, [
    ⟨3, 34, 5, 56, [(34,-1), (57,1), (91,-3), (35,-1), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (27,-3), (61,1), (62,1), (29,-1), (30,-1), (64,3), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1), (56,1)], 4⟩,
    ⟨5, 56, 1, 11, [(56,1), (34,-1), (57,1), (35,-1), (91,-3), (58,1), (36,-1), (59,1), (37,-1), (60,1), (38,-1), (27,-3), (61,1), (62,1), (29,-1), (30,-1), (64,3), (53,1), (31,-1), (54,1), (32,-1), (55,1), (33,-1)], 4⟩,
    ⟨1, 11, 5, 54, [(33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (91,-3), (37,-1), (59,1), (27,-3), (38,-1), (60,1), (61,1), (29,-1), (62,1), (30,-1), (31,-1), (53,1), (64,3), (32,-1), (54,1)], 4⟩,
    ⟨5, 54, 3, 32, [(54,1), (33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (37,-1), (91,-3), (59,1), (27,-3), (38,-1), (60,1), (61,1), (29,-1), (62,1), (30,-1), (31,-1), (53,1), (64,3), (32,-1)], 4⟩,
    ⟨3, 32, 5, 53, [(32,-1), (64,3), (54,1), (33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (37,-1), (27,-3), (59,1), (91,-3), (38,-1), (60,1), (29,-1), (61,1), (30,-1), (62,1), (31,-1), (53,1)], 4⟩,
    ⟨5, 53, 2, 21, [(53,1), (32,-1), (64,3), (54,1), (33,-1), (55,1), (34,-1), (56,1), (35,-1), (57,1), (36,-1), (58,1), (37,-1), (27,-3), (59,1), (38,-1), (91,-3), (60,1), (29,-1), (61,1), (30,-1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment25_checked : phiCertifiedSegment25.check=true := by decide +kernel

def phiCertifiedSegment26 : PhiCertifiedSegment :=
  ⟨(2/21), (9/91), 5, [
    ⟨2, 21, 3, 31, [(32,-1), (53,1), (64,3), (33,-1), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (58,1), (27,-3), (38,-1), (59,1), (91,-3), (60,1), (29,-1), (61,1), (30,-1), (62,1), (31,-1)], 5⟩,
    ⟨3, 31, 6, 61, [(31,-1), (62,1), (32,-1), (53,1), (33,-1), (64,3), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (27,-3), (58,1), (38,-1), (59,1), (29,-1), (60,1), (91,-3), (30,-1), (61,1)], 5⟩,
    ⟨6, 61, 9, 91, [(61,1), (31,-1), (62,1), (32,-1), (53,1), (33,-1), (64,3), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (27,-3), (58,1), (38,-1), (59,1), (29,-1), (60,1), (30,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment26_checked : phiCertifiedSegment26.check=true := by decide +kernel

def phiCertifiedSegment27 : PhiCertifiedSegment :=
  ⟨(9/91), (1/10), 8, [
    ⟨9, 91, 1, 10, [(91,-3), (61,1), (31,-1), (62,1), (32,-1), (53,1), (33,-1), (64,3), (54,1), (34,-1), (55,1), (35,-1), (56,1), (36,-1), (57,1), (37,-1), (27,-3), (58,1), (38,-1), (59,1), (29,-1), (60,1), (30,-1)], 8⟩]⟩

lemma phiCertifiedSegment27_checked : phiCertifiedSegment27.check=true := by decide +kernel

def phiCertifiedSegment28 : PhiCertifiedSegment :=
  ⟨(1/10), (3/29), 7, [
    ⟨1, 10, 6, 59, [(30,-1), (60,1), (31,-1), (61,1), (91,-3), (32,-1), (62,1), (33,-1), (53,1), (34,-1), (54,1), (64,3), (35,-1), (55,1), (36,-1), (56,1), (27,-3), (37,-1), (57,1), (38,-1), (58,1), (29,-1), (59,1)], 7⟩,
    ⟨6, 59, 3, 29, [(59,1), (30,-1), (60,1), (31,-1), (61,1), (32,-1), (91,-3), (62,1), (33,-1), (53,1), (34,-1), (54,1), (64,3), (35,-1), (55,1), (36,-1), (56,1), (27,-3), (37,-1), (57,1), (38,-1), (58,1), (29,-1)], 7⟩]⟩

lemma phiCertifiedSegment28_checked : phiCertifiedSegment28.check=true := by decide +kernel

def phiCertifiedSegment29 : PhiCertifiedSegment :=
  ⟨(3/29), (4/37), 8, [
    ⟨3, 29, 2, 19, [(29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (91,-3), (53,1), (34,-1), (54,1), (35,-1), (64,3), (55,1), (36,-1), (27,-3), (56,1), (37,-1), (57,1), (38,-1)], 8⟩,
    ⟨2, 19, 3, 28, [(38,-1), (57,1), (29,-1), (58,1), (30,-1), (59,1), (31,-1), (60,1), (32,-1), (61,1), (33,-1), (62,1), (34,-1), (53,1), (91,-3), (35,-1), (54,1), (64,3), (36,-1), (55,1), (27,-3), (37,-1), (56,1)], 8⟩,
    ⟨3, 28, 4, 37, [(56,1), (38,-1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (53,1), (35,-1), (91,-3), (54,1), (36,-1), (64,3), (27,-3), (55,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment29_checked : phiCertifiedSegment29.check=true := by decide +kernel

def phiCertifiedSegment30 : PhiCertifiedSegment :=
  ⟨(4/37), (10/91), 5, [
    ⟨4, 37, 6, 55, [(37,-1), (56,1), (38,-1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (53,1), (35,-1), (54,1), (91,-3), (36,-1), (27,-3), (64,3), (55,1)], 5⟩,
    ⟨6, 55, 7, 64, [(55,1), (37,-1), (56,1), (38,-1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (53,1), (35,-1), (54,1), (36,-1), (91,-3), (27,-3), (64,3)], 5⟩,
    ⟨7, 64, 10, 91, [(64,3), (55,1), (37,-1), (56,1), (38,-1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (53,1), (35,-1), (54,1), (36,-1), (27,-3), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment30_checked : phiCertifiedSegment30.check=true := by decide +kernel

def phiCertifiedSegment31 : PhiCertifiedSegment :=
  ⟨(10/91), (1/9), 8, [
    ⟨10, 91, 1, 9, [(91,-3), (64,3), (55,1), (37,-1), (56,1), (38,-1), (29,-1), (57,1), (30,-1), (58,1), (31,-1), (59,1), (32,-1), (60,1), (33,-1), (61,1), (34,-1), (62,1), (53,1), (35,-1), (54,1), (36,-1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment31_checked : phiCertifiedSegment31.check=true := by decide +kernel

def phiCertifiedSegment32 : PhiCertifiedSegment :=
  ⟨(1/9), (3/26), 4, [
    ⟨1, 9, 7, 62, [(27,-3), (36,-1), (54,1), (37,-1), (55,1), (64,3), (91,-3), (29,-1), (38,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (53,1), (62,1)], 4⟩,
    ⟨7, 62, 6, 53, [(62,1), (27,-3), (36,-1), (54,1), (37,-1), (55,1), (64,3), (29,-1), (91,-3), (38,-1), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1), (53,1)], 4⟩,
    ⟨6, 53, 4, 35, [(53,1), (62,1), (27,-3), (36,-1), (54,1), (37,-1), (55,1), (64,3), (29,-1), (38,-1), (91,-3), (56,1), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1), (35,-1)], 4⟩,
    ⟨4, 35, 7, 61, [(35,-1), (53,1), (27,-3), (62,1), (36,-1), (54,1), (37,-1), (55,1), (29,-1), (64,3), (38,-1), (56,1), (91,-3), (30,-1), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1), (61,1)], 4⟩,
    ⟨7, 61, 3, 26, [(61,1), (35,-1), (53,1), (27,-3), (62,1), (36,-1), (54,1), (37,-1), (55,1), (29,-1), (64,3), (38,-1), (56,1), (30,-1), (91,-3), (57,1), (31,-1), (58,1), (32,-1), (59,1), (33,-1), (60,1), (34,-1)], 4⟩]⟩

lemma phiCertifiedSegment32_checked : phiCertifiedSegment32.check=true := by decide +kernel

def phiCertifiedSegment33 : PhiCertifiedSegment :=
  ⟨(3/26), (2/17), 3, [
    ⟨3, 26, 7, 60, [(35,-1), (61,1), (27,-3), (53,1), (36,-1), (62,1), (54,1), (37,-1), (29,-1), (55,1), (38,-1), (64,3), (30,-1), (56,1), (91,-3), (31,-1), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1), (60,1)], 3⟩,
    ⟨7, 60, 2, 17, [(60,1), (35,-1), (61,1), (27,-3), (53,1), (36,-1), (62,1), (54,1), (37,-1), (29,-1), (55,1), (38,-1), (64,3), (30,-1), (56,1), (31,-1), (91,-3), (57,1), (32,-1), (58,1), (33,-1), (59,1), (34,-1)], 3⟩]⟩

lemma phiCertifiedSegment33_checked : phiCertifiedSegment33.check=true := by decide +kernel

def phiCertifiedSegment34 : PhiCertifiedSegment :=
  ⟨(2/17), (4/33), 4, [
    ⟨2, 17, 7, 59, [(34,-1), (60,1), (35,-1), (27,-3), (61,1), (36,-1), (53,1), (62,1), (37,-1), (54,1), (29,-1), (38,-1), (55,1), (30,-1), (64,3), (56,1), (31,-1), (57,1), (91,-3), (32,-1), (58,1), (33,-1), (59,1)], 4⟩,
    ⟨7, 59, 3, 25, [(59,1), (34,-1), (60,1), (35,-1), (27,-3), (61,1), (36,-1), (53,1), (62,1), (37,-1), (54,1), (29,-1), (38,-1), (55,1), (30,-1), (64,3), (56,1), (31,-1), (57,1), (32,-1), (91,-3), (58,1), (33,-1)], 4⟩,
    ⟨3, 25, 7, 58, [(34,-1), (59,1), (35,-1), (60,1), (27,-3), (36,-1), (61,1), (53,1), (37,-1), (62,1), (29,-1), (54,1), (38,-1), (30,-1), (55,1), (64,3), (31,-1), (56,1), (32,-1), (57,1), (91,-3), (33,-1), (58,1)], 4⟩,
    ⟨7, 58, 11, 91, [(58,1), (34,-1), (59,1), (35,-1), (60,1), (27,-3), (36,-1), (61,1), (53,1), (37,-1), (62,1), (29,-1), (54,1), (38,-1), (30,-1), (55,1), (64,3), (31,-1), (56,1), (32,-1), (57,1), (33,-1), (91,-3)], 4⟩,
    ⟨11, 91, 4, 33, [(91,-3), (58,1), (34,-1), (59,1), (35,-1), (60,1), (27,-3), (36,-1), (61,1), (53,1), (37,-1), (62,1), (29,-1), (54,1), (38,-1), (30,-1), (55,1), (64,3), (31,-1), (56,1), (32,-1), (57,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment34_checked : phiCertifiedSegment34.check=true := by decide +kernel

def phiCertifiedSegment35 : PhiCertifiedSegment :=
  ⟨(4/33), (1/8), 5, [
    ⟨4, 33, 7, 57, [(33,-1), (58,1), (91,-3), (34,-1), (59,1), (35,-1), (27,-3), (60,1), (36,-1), (61,1), (53,1), (37,-1), (29,-1), (62,1), (54,1), (38,-1), (30,-1), (55,1), (31,-1), (64,3), (56,1), (32,-1), (57,1)], 5⟩,
    ⟨7, 57, 1, 8, [(57,1), (33,-1), (58,1), (34,-1), (91,-3), (59,1), (35,-1), (27,-3), (60,1), (36,-1), (61,1), (53,1), (37,-1), (29,-1), (62,1), (54,1), (38,-1), (30,-1), (55,1), (31,-1), (64,3), (56,1), (32,-1)], 5⟩]⟩

lemma phiCertifiedSegment35_checked : phiCertifiedSegment35.check=true := by decide +kernel

def phiCertifiedSegment36 : PhiCertifiedSegment :=
  ⟨(1/8), (4/31), 3, [
    ⟨1, 8, 7, 55, [(32,-1), (56,1), (64,3), (33,-1), (57,1), (34,-1), (58,1), (27,-3), (35,-1), (59,1), (91,-3), (36,-1), (60,1), (29,-1), (37,-1), (53,1), (61,1), (30,-1), (38,-1), (54,1), (62,1), (31,-1), (55,1)], 3⟩,
    ⟨7, 55, 4, 31, [(55,1), (32,-1), (56,1), (64,3), (33,-1), (57,1), (34,-1), (58,1), (27,-3), (35,-1), (59,1), (36,-1), (91,-3), (60,1), (29,-1), (37,-1), (53,1), (61,1), (30,-1), (38,-1), (54,1), (62,1), (31,-1)], 3⟩]⟩

lemma phiCertifiedSegment36_checked : phiCertifiedSegment36.check=true := by decide +kernel

def phiCertifiedSegment37 : PhiCertifiedSegment :=
  ⟨(4/31), (5/38), 4, [
    ⟨4, 31, 7, 54, [(31,-1), (62,1), (55,1), (32,-1), (56,1), (33,-1), (64,3), (57,1), (34,-1), (27,-3), (58,1), (35,-1), (59,1), (36,-1), (29,-1), (60,1), (91,-3), (37,-1), (53,1), (30,-1), (61,1), (38,-1), (54,1)], 4⟩,
    ⟨7, 54, 3, 23, [(54,1), (31,-1), (62,1), (55,1), (32,-1), (56,1), (33,-1), (64,3), (57,1), (34,-1), (27,-3), (58,1), (35,-1), (59,1), (36,-1), (29,-1), (60,1), (37,-1), (91,-3), (53,1), (30,-1), (61,1), (38,-1)], 4⟩,
    ⟨3, 23, 8, 61, [(31,-1), (54,1), (62,1), (32,-1), (55,1), (33,-1), (56,1), (64,3), (34,-1), (57,1), (27,-3), (35,-1), (58,1), (36,-1), (59,1), (29,-1), (37,-1), (60,1), (91,-3), (30,-1), (53,1), (38,-1), (61,1)], 4⟩,
    ⟨8, 61, 5, 38, [(61,1), (31,-1), (54,1), (62,1), (32,-1), (55,1), (33,-1), (56,1), (64,3), (34,-1), (57,1), (27,-3), (35,-1), (58,1), (36,-1), (59,1), (29,-1), (37,-1), (60,1), (30,-1), (91,-3), (53,1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment37_checked : phiCertifiedSegment37.check=true := by decide +kernel

def phiCertifiedSegment38 : PhiCertifiedSegment :=
  ⟨(5/38), (12/91), 5, [
    ⟨5, 38, 12, 91, [(38,-1), (61,1), (31,-1), (54,1), (62,1), (32,-1), (55,1), (33,-1), (56,1), (64,3), (34,-1), (57,1), (27,-3), (35,-1), (58,1), (36,-1), (59,1), (29,-1), (37,-1), (60,1), (30,-1), (53,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment38_checked : phiCertifiedSegment38.check=true := by decide +kernel

def phiCertifiedSegment39 : PhiCertifiedSegment :=
  ⟨(12/91), (2/15), 7, [
    ⟨12, 91, 7, 53, [(91,-3), (38,-1), (61,1), (31,-1), (54,1), (62,1), (32,-1), (55,1), (33,-1), (56,1), (64,3), (34,-1), (57,1), (27,-3), (35,-1), (58,1), (36,-1), (59,1), (29,-1), (37,-1), (60,1), (30,-1), (53,1)], 7⟩,
    ⟨7, 53, 2, 15, [(53,1), (38,-1), (91,-3), (61,1), (31,-1), (54,1), (62,1), (32,-1), (55,1), (33,-1), (56,1), (64,3), (34,-1), (57,1), (27,-3), (35,-1), (58,1), (36,-1), (59,1), (29,-1), (37,-1), (60,1), (30,-1)], 7⟩]⟩

lemma phiCertifiedSegment39_checked : phiCertifiedSegment39.check=true := by decide +kernel

def phiCertifiedSegment40 : PhiCertifiedSegment :=
  ⟨(2/15), (5/37), 8, [
    ⟨2, 15, 5, 37, [(30,-1), (60,1), (38,-1), (53,1), (31,-1), (61,1), (91,-3), (54,1), (32,-1), (62,1), (55,1), (33,-1), (56,1), (34,-1), (64,3), (27,-3), (57,1), (35,-1), (58,1), (36,-1), (29,-1), (59,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment40_checked : phiCertifiedSegment40.check=true := by decide +kernel

def phiCertifiedSegment41 : PhiCertifiedSegment :=
  ⟨(5/37), (1/7), 6, [
    ⟨5, 37, 8, 59, [(37,-1), (30,-1), (60,1), (38,-1), (53,1), (31,-1), (61,1), (54,1), (91,-3), (32,-1), (62,1), (55,1), (33,-1), (56,1), (34,-1), (27,-3), (64,3), (57,1), (35,-1), (58,1), (36,-1), (29,-1), (59,1)], 6⟩,
    ⟨8, 59, 3, 22, [(59,1), (37,-1), (30,-1), (60,1), (38,-1), (53,1), (31,-1), (61,1), (54,1), (32,-1), (91,-3), (62,1), (55,1), (33,-1), (56,1), (34,-1), (27,-3), (64,3), (57,1), (35,-1), (58,1), (36,-1), (29,-1)], 6⟩,
    ⟨3, 22, 4, 29, [(37,-1), (59,1), (30,-1), (38,-1), (60,1), (31,-1), (53,1), (61,1), (32,-1), (54,1), (91,-3), (62,1), (33,-1), (55,1), (34,-1), (56,1), (27,-3), (64,3), (35,-1), (57,1), (36,-1), (58,1), (29,-1)], 6⟩,
    ⟨4, 29, 5, 36, [(29,-1), (58,1), (37,-1), (30,-1), (59,1), (38,-1), (31,-1), (60,1), (53,1), (32,-1), (61,1), (54,1), (33,-1), (62,1), (91,-3), (55,1), (34,-1), (27,-3), (56,1), (35,-1), (64,3), (57,1), (36,-1)], 6⟩,
    ⟨5, 36, 8, 57, [(36,-1), (29,-1), (58,1), (37,-1), (30,-1), (59,1), (38,-1), (31,-1), (60,1), (53,1), (32,-1), (61,1), (54,1), (33,-1), (62,1), (55,1), (91,-3), (34,-1), (27,-3), (56,1), (35,-1), (64,3), (57,1)], 6⟩,
    ⟨8, 57, 9, 64, [(57,1), (36,-1), (29,-1), (58,1), (37,-1), (30,-1), (59,1), (38,-1), (31,-1), (60,1), (53,1), (32,-1), (61,1), (54,1), (33,-1), (62,1), (55,1), (34,-1), (91,-3), (27,-3), (56,1), (35,-1), (64,3)], 6⟩,
    ⟨9, 64, 1, 7, [(64,3), (57,1), (36,-1), (29,-1), (58,1), (37,-1), (30,-1), (59,1), (38,-1), (31,-1), (60,1), (53,1), (32,-1), (61,1), (54,1), (33,-1), (62,1), (55,1), (34,-1), (27,-3), (91,-3), (56,1), (35,-1)], 6⟩]⟩

lemma phiCertifiedSegment41_checked : phiCertifiedSegment41.check=true := by decide +kernel

def phiCertifiedSegment42 : PhiCertifiedSegment :=
  ⟨(1/7), (4/27), 8, [
    ⟨1, 7, 9, 62, [(35,-1), (56,1), (91,-3), (29,-1), (36,-1), (57,1), (64,3), (30,-1), (37,-1), (58,1), (31,-1), (38,-1), (59,1), (32,-1), (53,1), (60,1), (33,-1), (54,1), (61,1), (27,-3), (34,-1), (55,1), (62,1)], 8⟩,
    ⟨9, 62, 8, 55, [(62,1), (35,-1), (56,1), (29,-1), (91,-3), (36,-1), (57,1), (64,3), (30,-1), (37,-1), (58,1), (31,-1), (38,-1), (59,1), (32,-1), (53,1), (60,1), (33,-1), (54,1), (61,1), (27,-3), (34,-1), (55,1)], 8⟩,
    ⟨8, 55, 5, 34, [(55,1), (62,1), (35,-1), (56,1), (29,-1), (36,-1), (91,-3), (57,1), (64,3), (30,-1), (37,-1), (58,1), (31,-1), (38,-1), (59,1), (32,-1), (53,1), (60,1), (33,-1), (54,1), (61,1), (27,-3), (34,-1)], 8⟩,
    ⟨5, 34, 9, 61, [(34,-1), (55,1), (62,1), (35,-1), (56,1), (29,-1), (36,-1), (57,1), (91,-3), (30,-1), (64,3), (37,-1), (58,1), (31,-1), (38,-1), (59,1), (32,-1), (53,1), (60,1), (33,-1), (54,1), (27,-3), (61,1)], 8⟩,
    ⟨9, 61, 4, 27, [(61,1), (34,-1), (55,1), (62,1), (35,-1), (56,1), (29,-1), (36,-1), (57,1), (30,-1), (91,-3), (64,3), (37,-1), (58,1), (31,-1), (38,-1), (59,1), (32,-1), (53,1), (60,1), (33,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment42_checked : phiCertifiedSegment42.check=true := by decide +kernel

def phiCertifiedSegment43 : PhiCertifiedSegment :=
  ⟨(4/27), (5/33), 3, [
    ⟨4, 27, 3, 20, [(27,-3), (54,1), (34,-1), (61,1), (55,1), (35,-1), (62,1), (29,-1), (56,1), (36,-1), (30,-1), (57,1), (37,-1), (64,3), (91,-3), (31,-1), (58,1), (38,-1), (32,-1), (59,1), (53,1), (33,-1), (60,1)], 3⟩,
    ⟨3, 20, 8, 53, [(60,1), (27,-3), (34,-1), (54,1), (61,1), (35,-1), (55,1), (62,1), (29,-1), (36,-1), (56,1), (30,-1), (37,-1), (57,1), (64,3), (31,-1), (91,-3), (38,-1), (58,1), (32,-1), (59,1), (33,-1), (53,1)], 3⟩,
    ⟨8, 53, 5, 33, [(53,1), (60,1), (27,-3), (34,-1), (54,1), (61,1), (35,-1), (55,1), (62,1), (29,-1), (36,-1), (56,1), (30,-1), (37,-1), (57,1), (64,3), (31,-1), (38,-1), (91,-3), (58,1), (32,-1), (59,1), (33,-1)], 3⟩]⟩

lemma phiCertifiedSegment43_checked : phiCertifiedSegment43.check=true := by decide +kernel

def phiCertifiedSegment44 : PhiCertifiedSegment :=
  ⟨(5/33), (3/19), 4, [
    ⟨5, 33, 9, 59, [(33,-1), (53,1), (27,-3), (60,1), (34,-1), (54,1), (61,1), (35,-1), (55,1), (29,-1), (62,1), (36,-1), (56,1), (30,-1), (37,-1), (57,1), (31,-1), (64,3), (38,-1), (58,1), (91,-3), (32,-1), (59,1)], 4⟩,
    ⟨9, 59, 2, 13, [(59,1), (33,-1), (53,1), (27,-3), (60,1), (34,-1), (54,1), (61,1), (35,-1), (55,1), (29,-1), (62,1), (36,-1), (56,1), (30,-1), (37,-1), (57,1), (31,-1), (64,3), (38,-1), (58,1), (32,-1), (91,-3)], 4⟩,
    ⟨2, 13, 9, 58, [(91,-3), (33,-1), (59,1), (27,-3), (53,1), (34,-1), (60,1), (54,1), (35,-1), (61,1), (29,-1), (55,1), (36,-1), (62,1), (30,-1), (56,1), (37,-1), (31,-1), (57,1), (38,-1), (64,3), (32,-1), (58,1)], 4⟩,
    ⟨9, 58, 5, 32, [(58,1), (33,-1), (91,-3), (59,1), (27,-3), (53,1), (34,-1), (60,1), (54,1), (35,-1), (61,1), (29,-1), (55,1), (36,-1), (62,1), (30,-1), (56,1), (37,-1), (31,-1), (57,1), (38,-1), (64,3), (32,-1)], 4⟩,
    ⟨5, 32, 3, 19, [(32,-1), (64,3), (58,1), (33,-1), (27,-3), (59,1), (91,-3), (53,1), (34,-1), (60,1), (54,1), (35,-1), (29,-1), (61,1), (55,1), (36,-1), (30,-1), (62,1), (56,1), (37,-1), (31,-1), (57,1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment44_checked : phiCertifiedSegment44.check=true := by decide +kernel

def phiCertifiedSegment45 : PhiCertifiedSegment :=
  ⟨(3/19), (1/6), 5, [
    ⟨3, 19, 4, 25, [(38,-1), (57,1), (32,-1), (64,3), (58,1), (33,-1), (27,-3), (59,1), (34,-1), (53,1), (91,-3), (60,1), (35,-1), (54,1), (29,-1), (61,1), (36,-1), (55,1), (30,-1), (62,1), (37,-1), (56,1), (31,-1)], 5⟩,
    ⟨4, 25, 9, 56, [(38,-1), (32,-1), (57,1), (64,3), (33,-1), (58,1), (27,-3), (34,-1), (59,1), (53,1), (91,-3), (35,-1), (60,1), (29,-1), (54,1), (36,-1), (61,1), (30,-1), (55,1), (37,-1), (62,1), (31,-1), (56,1)], 5⟩,
    ⟨9, 56, 5, 31, [(56,1), (38,-1), (32,-1), (57,1), (64,3), (33,-1), (58,1), (27,-3), (34,-1), (59,1), (53,1), (35,-1), (91,-3), (60,1), (29,-1), (54,1), (36,-1), (61,1), (30,-1), (55,1), (37,-1), (62,1), (31,-1)], 5⟩,
    ⟨5, 31, 6, 37, [(31,-1), (62,1), (56,1), (38,-1), (32,-1), (57,1), (33,-1), (64,3), (27,-3), (58,1), (34,-1), (59,1), (53,1), (35,-1), (29,-1), (60,1), (91,-3), (54,1), (36,-1), (30,-1), (61,1), (55,1), (37,-1)], 5⟩,
    ⟨6, 37, 9, 55, [(37,-1), (31,-1), (62,1), (56,1), (38,-1), (32,-1), (57,1), (33,-1), (27,-3), (64,3), (58,1), (34,-1), (59,1), (53,1), (35,-1), (29,-1), (60,1), (54,1), (91,-3), (36,-1), (30,-1), (61,1), (55,1)], 5⟩,
    ⟨9, 55, 10, 61, [(55,1), (37,-1), (31,-1), (62,1), (56,1), (38,-1), (32,-1), (57,1), (33,-1), (27,-3), (64,3), (58,1), (34,-1), (59,1), (53,1), (35,-1), (29,-1), (60,1), (54,1), (36,-1), (91,-3), (30,-1), (61,1)], 5⟩,
    ⟨10, 61, 15, 91, [(61,1), (55,1), (37,-1), (31,-1), (62,1), (56,1), (38,-1), (32,-1), (57,1), (33,-1), (27,-3), (64,3), (58,1), (34,-1), (59,1), (53,1), (35,-1), (29,-1), (60,1), (54,1), (36,-1), (30,-1), (91,-3)], 5⟩,
    ⟨15, 91, 1, 6, [(91,-3), (61,1), (55,1), (37,-1), (31,-1), (62,1), (56,1), (38,-1), (32,-1), (57,1), (33,-1), (27,-3), (64,3), (58,1), (34,-1), (59,1), (53,1), (35,-1), (29,-1), (60,1), (54,1), (36,-1), (30,-1)], 5⟩]⟩

lemma phiCertifiedSegment45_checked : phiCertifiedSegment45.check=true := by decide +kernel

def phiCertifiedSegment46 : PhiCertifiedSegment :=
  ⟨(1/6), (5/29), 4, [
    ⟨1, 6, 10, 59, [(30,-1), (36,-1), (54,1), (60,1), (31,-1), (37,-1), (55,1), (61,1), (91,-3), (32,-1), (38,-1), (56,1), (62,1), (27,-3), (33,-1), (57,1), (34,-1), (58,1), (64,3), (29,-1), (35,-1), (53,1), (59,1)], 4⟩,
    ⟨10, 59, 9, 53, [(59,1), (30,-1), (36,-1), (54,1), (60,1), (31,-1), (37,-1), (55,1), (61,1), (32,-1), (91,-3), (38,-1), (56,1), (62,1), (27,-3), (33,-1), (57,1), (34,-1), (58,1), (64,3), (29,-1), (35,-1), (53,1)], 4⟩,
    ⟨9, 53, 6, 35, [(53,1), (59,1), (30,-1), (36,-1), (54,1), (60,1), (31,-1), (37,-1), (55,1), (61,1), (32,-1), (38,-1), (91,-3), (56,1), (62,1), (27,-3), (33,-1), (57,1), (34,-1), (58,1), (64,3), (29,-1), (35,-1)], 4⟩,
    ⟨6, 35, 11, 64, [(35,-1), (53,1), (59,1), (30,-1), (36,-1), (54,1), (60,1), (31,-1), (37,-1), (55,1), (61,1), (32,-1), (38,-1), (56,1), (91,-3), (27,-3), (62,1), (33,-1), (57,1), (34,-1), (58,1), (29,-1), (64,3)], 4⟩,
    ⟨11, 64, 5, 29, [(64,3), (35,-1), (53,1), (59,1), (30,-1), (36,-1), (54,1), (60,1), (31,-1), (37,-1), (55,1), (61,1), (32,-1), (38,-1), (56,1), (27,-3), (91,-3), (62,1), (33,-1), (57,1), (34,-1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment46_checked : phiCertifiedSegment46.check=true := by decide +kernel

def phiCertifiedSegment47 : PhiCertifiedSegment :=
  ⟨(5/29), (16/91), 5, [
    ⟨5, 29, 4, 23, [(29,-1), (58,1), (35,-1), (64,3), (53,1), (30,-1), (59,1), (36,-1), (54,1), (31,-1), (60,1), (37,-1), (55,1), (32,-1), (61,1), (38,-1), (27,-3), (56,1), (33,-1), (62,1), (91,-3), (57,1), (34,-1)], 5⟩,
    ⟨4, 23, 10, 57, [(29,-1), (35,-1), (58,1), (64,3), (30,-1), (53,1), (36,-1), (59,1), (31,-1), (54,1), (37,-1), (60,1), (32,-1), (55,1), (38,-1), (61,1), (27,-3), (33,-1), (56,1), (62,1), (91,-3), (34,-1), (57,1)], 5⟩,
    ⟨10, 57, 16, 91, [(57,1), (29,-1), (35,-1), (58,1), (64,3), (30,-1), (53,1), (36,-1), (59,1), (31,-1), (54,1), (37,-1), (60,1), (32,-1), (55,1), (38,-1), (61,1), (27,-3), (33,-1), (56,1), (62,1), (34,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment47_checked : phiCertifiedSegment47.check=true := by decide +kernel

def phiCertifiedSegment48 : PhiCertifiedSegment :=
  ⟨(16/91), (3/17), 7, [
    ⟨16, 91, 3, 17, [(91,-3), (57,1), (29,-1), (35,-1), (58,1), (64,3), (30,-1), (53,1), (36,-1), (59,1), (31,-1), (54,1), (37,-1), (60,1), (32,-1), (55,1), (38,-1), (61,1), (27,-3), (33,-1), (56,1), (62,1), (34,-1)], 7⟩]⟩

lemma phiCertifiedSegment48_checked : phiCertifiedSegment48.check=true := by decide +kernel

def phiCertifiedSegment49 : PhiCertifiedSegment :=
  ⟨(3/17), (5/28), 8, [
    ⟨3, 17, 11, 62, [(34,-1), (57,1), (91,-3), (29,-1), (35,-1), (58,1), (30,-1), (64,3), (36,-1), (53,1), (59,1), (31,-1), (37,-1), (54,1), (60,1), (32,-1), (38,-1), (55,1), (27,-3), (61,1), (33,-1), (56,1), (62,1)], 8⟩,
    ⟨11, 62, 5, 28, [(62,1), (34,-1), (57,1), (29,-1), (91,-3), (35,-1), (58,1), (30,-1), (64,3), (36,-1), (53,1), (59,1), (31,-1), (37,-1), (54,1), (60,1), (32,-1), (38,-1), (55,1), (27,-3), (61,1), (33,-1), (56,1)], 8⟩]⟩

lemma phiCertifiedSegment49_checked : phiCertifiedSegment49.check=true := by decide +kernel

def phiCertifiedSegment50 : PhiCertifiedSegment :=
  ⟨(5/28), (7/38), 7, [
    ⟨5, 28, 11, 61, [(56,1), (34,-1), (62,1), (29,-1), (57,1), (35,-1), (91,-3), (30,-1), (58,1), (36,-1), (64,3), (53,1), (31,-1), (59,1), (37,-1), (54,1), (32,-1), (60,1), (38,-1), (27,-3), (55,1), (33,-1), (61,1)], 7⟩,
    ⟨11, 61, 2, 11, [(61,1), (56,1), (34,-1), (62,1), (29,-1), (57,1), (35,-1), (30,-1), (91,-3), (58,1), (36,-1), (64,3), (53,1), (31,-1), (59,1), (37,-1), (54,1), (32,-1), (60,1), (38,-1), (27,-3), (55,1), (33,-1)], 7⟩,
    ⟨2, 11, 11, 60, [(33,-1), (55,1), (61,1), (34,-1), (56,1), (29,-1), (62,1), (35,-1), (57,1), (30,-1), (36,-1), (58,1), (91,-3), (31,-1), (53,1), (64,3), (37,-1), (59,1), (32,-1), (54,1), (27,-3), (38,-1), (60,1)], 7⟩,
    ⟨11, 60, 7, 38, [(60,1), (33,-1), (55,1), (61,1), (34,-1), (56,1), (29,-1), (62,1), (35,-1), (57,1), (30,-1), (36,-1), (58,1), (31,-1), (91,-3), (53,1), (64,3), (37,-1), (59,1), (32,-1), (54,1), (27,-3), (38,-1)], 7⟩]⟩

lemma phiCertifiedSegment50_checked : phiCertifiedSegment50.check=true := by decide +kernel

def phiCertifiedSegment51 : PhiCertifiedSegment :=
  ⟨(7/38), (5/27), 8, [
    ⟨7, 38, 5, 27, [(38,-1), (60,1), (33,-1), (55,1), (61,1), (34,-1), (56,1), (29,-1), (62,1), (35,-1), (57,1), (30,-1), (36,-1), (58,1), (31,-1), (53,1), (91,-3), (64,3), (37,-1), (59,1), (32,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment51_checked : phiCertifiedSegment51.check=true := by decide +kernel

def phiCertifiedSegment52 : PhiCertifiedSegment :=
  ⟨(5/27), (4/21), 4, [
    ⟨5, 27, 11, 59, [(27,-3), (54,1), (38,-1), (33,-1), (60,1), (55,1), (34,-1), (61,1), (29,-1), (56,1), (35,-1), (62,1), (30,-1), (57,1), (36,-1), (31,-1), (58,1), (53,1), (37,-1), (64,3), (91,-3), (32,-1), (59,1)], 4⟩,
    ⟨11, 59, 17, 91, [(59,1), (27,-3), (54,1), (38,-1), (33,-1), (60,1), (55,1), (34,-1), (61,1), (29,-1), (56,1), (35,-1), (62,1), (30,-1), (57,1), (36,-1), (31,-1), (58,1), (53,1), (37,-1), (64,3), (32,-1), (91,-3)], 4⟩,
    ⟨17, 91, 3, 16, [(91,-3), (59,1), (27,-3), (54,1), (38,-1), (33,-1), (60,1), (55,1), (34,-1), (61,1), (29,-1), (56,1), (35,-1), (62,1), (30,-1), (57,1), (36,-1), (31,-1), (58,1), (53,1), (37,-1), (64,3), (32,-1)], 4⟩,
    ⟨3, 16, 10, 53, [(32,-1), (64,3), (27,-3), (59,1), (91,-3), (38,-1), (54,1), (33,-1), (60,1), (55,1), (34,-1), (29,-1), (61,1), (56,1), (35,-1), (30,-1), (62,1), (57,1), (36,-1), (31,-1), (58,1), (37,-1), (53,1)], 4⟩,
    ⟨10, 53, 7, 37, [(53,1), (32,-1), (64,3), (27,-3), (59,1), (38,-1), (91,-3), (54,1), (33,-1), (60,1), (55,1), (34,-1), (29,-1), (61,1), (56,1), (35,-1), (30,-1), (62,1), (57,1), (36,-1), (31,-1), (58,1), (37,-1)], 4⟩,
    ⟨7, 37, 11, 58, [(37,-1), (53,1), (32,-1), (27,-3), (64,3), (59,1), (38,-1), (54,1), (91,-3), (33,-1), (60,1), (55,1), (34,-1), (29,-1), (61,1), (56,1), (35,-1), (30,-1), (62,1), (57,1), (36,-1), (31,-1), (58,1)], 4⟩,
    ⟨11, 58, 4, 21, [(58,1), (37,-1), (53,1), (32,-1), (27,-3), (64,3), (59,1), (38,-1), (54,1), (33,-1), (91,-3), (60,1), (55,1), (34,-1), (29,-1), (61,1), (56,1), (35,-1), (30,-1), (62,1), (57,1), (36,-1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment52_checked : phiCertifiedSegment52.check=true := by decide +kernel

def phiCertifiedSegment53 : PhiCertifiedSegment :=
  ⟨(4/21), (5/26), 5, [
    ⟨4, 21, 5, 26, [(37,-1), (58,1), (32,-1), (53,1), (27,-3), (64,3), (38,-1), (59,1), (33,-1), (54,1), (91,-3), (60,1), (34,-1), (55,1), (29,-1), (61,1), (35,-1), (56,1), (30,-1), (62,1), (36,-1), (57,1), (31,-1)], 5⟩]⟩

lemma phiCertifiedSegment53_checked : phiCertifiedSegment53.check=true := by decide +kernel

def phiCertifiedSegment54 : PhiCertifiedSegment :=
  ⟨(5/26), (6/29), 4, [
    ⟨5, 26, 11, 57, [(37,-1), (32,-1), (58,1), (27,-3), (53,1), (38,-1), (64,3), (33,-1), (59,1), (54,1), (91,-3), (34,-1), (60,1), (29,-1), (55,1), (35,-1), (61,1), (30,-1), (56,1), (36,-1), (62,1), (31,-1), (57,1)], 4⟩,
    ⟨11, 57, 6, 31, [(57,1), (37,-1), (32,-1), (58,1), (27,-3), (53,1), (38,-1), (64,3), (33,-1), (59,1), (54,1), (34,-1), (91,-3), (60,1), (29,-1), (55,1), (35,-1), (61,1), (30,-1), (56,1), (36,-1), (62,1), (31,-1)], 4⟩,
    ⟨6, 31, 7, 36, [(31,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (60,1), (91,-3), (55,1), (35,-1), (30,-1), (61,1), (56,1), (36,-1)], 4⟩,
    ⟨7, 36, 11, 56, [(36,-1), (31,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (60,1), (55,1), (91,-3), (35,-1), (30,-1), (61,1), (56,1)], 4⟩,
    ⟨11, 56, 12, 61, [(56,1), (36,-1), (31,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (60,1), (55,1), (35,-1), (91,-3), (30,-1), (61,1)], 4⟩,
    ⟨12, 61, 18, 91, [(61,1), (56,1), (36,-1), (31,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (60,1), (55,1), (35,-1), (30,-1), (91,-3)], 4⟩,
    ⟨18, 91, 1, 5, [(91,-3), (61,1), (56,1), (36,-1), (31,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (60,1), (55,1), (35,-1), (30,-1)], 4⟩,
    ⟨1, 5, 13, 64, [(30,-1), (35,-1), (55,1), (60,1), (31,-1), (36,-1), (56,1), (61,1), (91,-3), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (33,-1), (38,-1), (53,1), (58,1), (29,-1), (34,-1), (54,1), (59,1), (64,3)], 4⟩,
    ⟨13, 64, 12, 59, [(64,3), (30,-1), (35,-1), (55,1), (60,1), (31,-1), (36,-1), (56,1), (61,1), (27,-3), (91,-3), (32,-1), (37,-1), (57,1), (62,1), (33,-1), (38,-1), (53,1), (58,1), (29,-1), (34,-1), (54,1), (59,1)], 4⟩,
    ⟨12, 59, 11, 54, [(59,1), (64,3), (30,-1), (35,-1), (55,1), (60,1), (31,-1), (36,-1), (56,1), (61,1), (27,-3), (32,-1), (91,-3), (37,-1), (57,1), (62,1), (33,-1), (38,-1), (53,1), (58,1), (29,-1), (34,-1), (54,1)], 4⟩,
    ⟨11, 54, 7, 34, [(54,1), (59,1), (64,3), (30,-1), (35,-1), (55,1), (60,1), (31,-1), (36,-1), (56,1), (61,1), (27,-3), (32,-1), (37,-1), (91,-3), (57,1), (62,1), (33,-1), (38,-1), (53,1), (58,1), (29,-1), (34,-1)], 4⟩,
    ⟨7, 34, 6, 29, [(34,-1), (54,1), (59,1), (30,-1), (64,3), (35,-1), (55,1), (60,1), (31,-1), (36,-1), (56,1), (27,-3), (61,1), (32,-1), (37,-1), (57,1), (91,-3), (62,1), (33,-1), (38,-1), (53,1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment54_checked : phiCertifiedSegment54.check=true := by decide +kernel

def phiCertifiedSegment55 : PhiCertifiedSegment :=
  ⟨(6/29), (19/91), 5, [
    ⟨6, 29, 11, 53, [(29,-1), (58,1), (34,-1), (54,1), (30,-1), (59,1), (35,-1), (64,3), (55,1), (31,-1), (60,1), (36,-1), (27,-3), (56,1), (32,-1), (61,1), (37,-1), (57,1), (33,-1), (62,1), (91,-3), (38,-1), (53,1)], 5⟩,
    ⟨11, 53, 5, 24, [(53,1), (29,-1), (58,1), (34,-1), (54,1), (30,-1), (59,1), (35,-1), (64,3), (55,1), (31,-1), (60,1), (36,-1), (27,-3), (56,1), (32,-1), (61,1), (37,-1), (57,1), (33,-1), (62,1), (38,-1), (91,-3)], 5⟩,
    ⟨5, 24, 19, 91, [(29,-1), (53,1), (34,-1), (58,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (31,-1), (55,1), (36,-1), (60,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (33,-1), (57,1), (38,-1), (62,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment55_checked : phiCertifiedSegment55.check=true := by decide +kernel

def phiCertifiedSegment56 : PhiCertifiedSegment :=
  ⟨(19/91), (7/33), 7, [
    ⟨19, 91, 13, 62, [(91,-3), (29,-1), (53,1), (34,-1), (58,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (31,-1), (55,1), (36,-1), (60,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (33,-1), (57,1), (38,-1), (62,1)], 7⟩,
    ⟨13, 62, 4, 19, [(62,1), (29,-1), (91,-3), (53,1), (34,-1), (58,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (31,-1), (55,1), (36,-1), (60,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (33,-1), (57,1), (38,-1)], 7⟩,
    ⟨4, 19, 7, 33, [(38,-1), (57,1), (62,1), (29,-1), (34,-1), (53,1), (91,-3), (58,1), (30,-1), (35,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (56,1), (61,1), (33,-1)], 7⟩]⟩

lemma phiCertifiedSegment56_checked : phiCertifiedSegment56.check=true := by decide +kernel

def phiCertifiedSegment57 : PhiCertifiedSegment :=
  ⟨(7/33), (8/37), 8, [
    ⟨7, 33, 13, 61, [(33,-1), (38,-1), (57,1), (29,-1), (62,1), (34,-1), (53,1), (58,1), (91,-3), (30,-1), (35,-1), (54,1), (59,1), (31,-1), (64,3), (36,-1), (55,1), (27,-3), (60,1), (32,-1), (37,-1), (56,1), (61,1)], 8⟩,
    ⟨13, 61, 3, 14, [(61,1), (33,-1), (38,-1), (57,1), (29,-1), (62,1), (34,-1), (53,1), (58,1), (30,-1), (91,-3), (35,-1), (54,1), (59,1), (31,-1), (64,3), (36,-1), (55,1), (27,-3), (60,1), (32,-1), (37,-1), (56,1)], 8⟩,
    ⟨3, 14, 8, 37, [(56,1), (33,-1), (61,1), (38,-1), (29,-1), (57,1), (34,-1), (62,1), (53,1), (30,-1), (58,1), (35,-1), (91,-3), (54,1), (31,-1), (59,1), (36,-1), (64,3), (27,-3), (55,1), (32,-1), (60,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment57_checked : phiCertifiedSegment57.check=true := by decide +kernel

def phiCertifiedSegment58 : PhiCertifiedSegment :=
  ⟨(8/37), (5/23), 5, [
    ⟨8, 37, 13, 60, [(37,-1), (56,1), (33,-1), (61,1), (38,-1), (29,-1), (57,1), (34,-1), (62,1), (53,1), (30,-1), (58,1), (35,-1), (54,1), (91,-3), (31,-1), (59,1), (36,-1), (27,-3), (64,3), (55,1), (32,-1), (60,1)], 5⟩,
    ⟨13, 60, 5, 23, [(60,1), (37,-1), (56,1), (33,-1), (61,1), (38,-1), (29,-1), (57,1), (34,-1), (62,1), (53,1), (30,-1), (58,1), (35,-1), (54,1), (31,-1), (91,-3), (59,1), (36,-1), (27,-3), (64,3), (55,1), (32,-1)], 5⟩]⟩

lemma phiCertifiedSegment58_checked : phiCertifiedSegment58.check=true := by decide +kernel

def phiCertifiedSegment59 : PhiCertifiedSegment :=
  ⟨(5/23), (20/91), 6, [
    ⟨5, 23, 12, 55, [(37,-1), (60,1), (33,-1), (56,1), (38,-1), (61,1), (29,-1), (34,-1), (57,1), (62,1), (30,-1), (53,1), (35,-1), (58,1), (31,-1), (54,1), (91,-3), (36,-1), (59,1), (27,-3), (64,3), (32,-1), (55,1)], 6⟩,
    ⟨12, 55, 7, 32, [(55,1), (37,-1), (60,1), (33,-1), (56,1), (38,-1), (61,1), (29,-1), (34,-1), (57,1), (62,1), (30,-1), (53,1), (35,-1), (58,1), (31,-1), (54,1), (36,-1), (91,-3), (59,1), (27,-3), (64,3), (32,-1)], 6⟩,
    ⟨7, 32, 20, 91, [(32,-1), (64,3), (55,1), (37,-1), (60,1), (33,-1), (56,1), (38,-1), (29,-1), (61,1), (34,-1), (57,1), (30,-1), (62,1), (53,1), (35,-1), (58,1), (31,-1), (54,1), (36,-1), (27,-3), (59,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment59_checked : phiCertifiedSegment59.check=true := by decide +kernel

def phiCertifiedSegment60 : PhiCertifiedSegment :=
  ⟨(20/91), (2/9), 8, [
    ⟨20, 91, 13, 59, [(91,-3), (32,-1), (64,3), (55,1), (37,-1), (60,1), (33,-1), (56,1), (38,-1), (29,-1), (61,1), (34,-1), (57,1), (30,-1), (62,1), (53,1), (35,-1), (58,1), (31,-1), (54,1), (36,-1), (27,-3), (59,1)], 8⟩,
    ⟨13, 59, 2, 9, [(59,1), (32,-1), (91,-3), (64,3), (55,1), (37,-1), (60,1), (33,-1), (56,1), (38,-1), (29,-1), (61,1), (34,-1), (57,1), (30,-1), (62,1), (53,1), (35,-1), (58,1), (31,-1), (54,1), (36,-1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment60_checked : phiCertifiedSegment60.check=true := by decide +kernel

def phiCertifiedSegment61 : PhiCertifiedSegment :=
  ⟨(2/9), (7/30), 4, [
    ⟨2, 9, 13, 58, [(27,-3), (36,-1), (54,1), (32,-1), (59,1), (37,-1), (55,1), (64,3), (91,-3), (33,-1), (60,1), (29,-1), (38,-1), (56,1), (34,-1), (61,1), (30,-1), (57,1), (35,-1), (53,1), (62,1), (31,-1), (58,1)], 4⟩,
    ⟨13, 58, 7, 31, [(58,1), (27,-3), (36,-1), (54,1), (32,-1), (59,1), (37,-1), (55,1), (64,3), (33,-1), (91,-3), (60,1), (29,-1), (38,-1), (56,1), (34,-1), (61,1), (30,-1), (57,1), (35,-1), (53,1), (62,1), (31,-1)], 4⟩,
    ⟨7, 31, 12, 53, [(31,-1), (62,1), (27,-3), (58,1), (36,-1), (54,1), (32,-1), (59,1), (37,-1), (55,1), (33,-1), (64,3), (29,-1), (60,1), (91,-3), (38,-1), (56,1), (34,-1), (30,-1), (61,1), (57,1), (35,-1), (53,1)], 4⟩,
    ⟨12, 53, 5, 22, [(53,1), (31,-1), (62,1), (27,-3), (58,1), (36,-1), (54,1), (32,-1), (59,1), (37,-1), (55,1), (33,-1), (64,3), (29,-1), (60,1), (38,-1), (91,-3), (56,1), (34,-1), (30,-1), (61,1), (57,1), (35,-1)], 4⟩,
    ⟨5, 22, 13, 57, [(31,-1), (53,1), (62,1), (27,-3), (36,-1), (58,1), (32,-1), (54,1), (37,-1), (59,1), (33,-1), (55,1), (64,3), (29,-1), (38,-1), (60,1), (91,-3), (34,-1), (56,1), (30,-1), (61,1), (35,-1), (57,1)], 4⟩,
    ⟨13, 57, 8, 35, [(57,1), (31,-1), (53,1), (62,1), (27,-3), (36,-1), (58,1), (32,-1), (54,1), (37,-1), (59,1), (33,-1), (55,1), (64,3), (29,-1), (38,-1), (60,1), (34,-1), (91,-3), (56,1), (30,-1), (61,1), (35,-1)], 4⟩,
    ⟨8, 35, 14, 61, [(35,-1), (57,1), (31,-1), (53,1), (27,-3), (62,1), (36,-1), (58,1), (32,-1), (54,1), (37,-1), (59,1), (33,-1), (55,1), (29,-1), (64,3), (38,-1), (60,1), (34,-1), (56,1), (91,-3), (30,-1), (61,1)], 4⟩,
    ⟨14, 61, 3, 13, [(61,1), (35,-1), (57,1), (31,-1), (53,1), (27,-3), (62,1), (36,-1), (58,1), (32,-1), (54,1), (37,-1), (59,1), (33,-1), (55,1), (29,-1), (64,3), (38,-1), (60,1), (34,-1), (56,1), (30,-1), (91,-3)], 4⟩,
    ⟨3, 13, 13, 56, [(91,-3), (35,-1), (61,1), (31,-1), (57,1), (27,-3), (53,1), (36,-1), (62,1), (32,-1), (58,1), (54,1), (37,-1), (33,-1), (59,1), (29,-1), (55,1), (38,-1), (64,3), (34,-1), (60,1), (30,-1), (56,1)], 4⟩,
    ⟨13, 56, 7, 30, [(56,1), (35,-1), (91,-3), (61,1), (31,-1), (57,1), (27,-3), (53,1), (36,-1), (62,1), (32,-1), (58,1), (54,1), (37,-1), (33,-1), (59,1), (29,-1), (55,1), (38,-1), (64,3), (34,-1), (60,1), (30,-1)], 4⟩]⟩

lemma phiCertifiedSegment61_checked : phiCertifiedSegment61.check=true := by decide +kernel

def phiCertifiedSegment62 : PhiCertifiedSegment :=
  ⟨(7/30), (4/17), 3, [
    ⟨7, 30, 15, 64, [(30,-1), (60,1), (56,1), (35,-1), (31,-1), (61,1), (91,-3), (27,-3), (57,1), (53,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (38,-1), (34,-1), (64,3)], 3⟩,
    ⟨15, 64, 4, 17, [(64,3), (30,-1), (60,1), (56,1), (35,-1), (31,-1), (61,1), (27,-3), (91,-3), (57,1), (53,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (38,-1), (34,-1)], 3⟩]⟩

lemma phiCertifiedSegment62_checked : phiCertifiedSegment62.check=true := by decide +kernel

def phiCertifiedSegment63 : PhiCertifiedSegment :=
  ⟨(4/17), (5/21), 4, [
    ⟨4, 17, 13, 55, [(34,-1), (30,-1), (64,3), (60,1), (56,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (91,-3), (36,-1), (53,1), (32,-1), (62,1), (58,1), (37,-1), (54,1), (33,-1), (29,-1), (59,1), (38,-1), (55,1)], 4⟩,
    ⟨13, 55, 9, 38, [(55,1), (34,-1), (30,-1), (64,3), (60,1), (56,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (36,-1), (91,-3), (53,1), (32,-1), (62,1), (58,1), (37,-1), (54,1), (33,-1), (29,-1), (59,1), (38,-1)], 4⟩,
    ⟨9, 38, 14, 59, [(38,-1), (55,1), (34,-1), (30,-1), (64,3), (60,1), (56,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (36,-1), (53,1), (91,-3), (32,-1), (62,1), (58,1), (37,-1), (54,1), (33,-1), (29,-1), (59,1)], 4⟩,
    ⟨14, 59, 5, 21, [(59,1), (38,-1), (55,1), (34,-1), (30,-1), (64,3), (60,1), (56,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (36,-1), (53,1), (32,-1), (91,-3), (62,1), (58,1), (37,-1), (54,1), (33,-1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment63_checked : phiCertifiedSegment63.check=true := by decide +kernel

def phiCertifiedSegment64 : PhiCertifiedSegment :=
  ⟨(5/21), (7/29), 5, [
    ⟨5, 21, 6, 25, [(38,-1), (59,1), (34,-1), (55,1), (30,-1), (64,3), (60,1), (35,-1), (56,1), (31,-1), (27,-3), (61,1), (36,-1), (57,1), (32,-1), (53,1), (91,-3), (62,1), (37,-1), (58,1), (33,-1), (54,1), (29,-1)], 5⟩,
    ⟨6, 25, 13, 54, [(38,-1), (34,-1), (59,1), (30,-1), (55,1), (64,3), (35,-1), (60,1), (31,-1), (56,1), (27,-3), (36,-1), (61,1), (32,-1), (57,1), (53,1), (91,-3), (37,-1), (62,1), (33,-1), (58,1), (29,-1), (54,1)], 5⟩,
    ⟨13, 54, 7, 29, [(54,1), (38,-1), (34,-1), (59,1), (30,-1), (55,1), (64,3), (35,-1), (60,1), (31,-1), (56,1), (27,-3), (36,-1), (61,1), (32,-1), (57,1), (53,1), (37,-1), (91,-3), (62,1), (33,-1), (58,1), (29,-1)], 5⟩]⟩

lemma phiCertifiedSegment64_checked : phiCertifiedSegment64.check=true := by decide +kernel

def phiCertifiedSegment65 : PhiCertifiedSegment :=
  ⟨(7/29), (22/91), 6, [
    ⟨7, 29, 22, 91, [(29,-1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (64,3), (31,-1), (60,1), (27,-3), (56,1), (36,-1), (32,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (62,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment65_checked : phiCertifiedSegment65.check=true := by decide +kernel

def phiCertifiedSegment66 : PhiCertifiedSegment :=
  ⟨(22/91), (8/33), 7, [
    ⟨22, 91, 15, 62, [(91,-3), (29,-1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (64,3), (31,-1), (60,1), (27,-3), (56,1), (36,-1), (32,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (62,1)], 7⟩,
    ⟨15, 62, 8, 33, [(62,1), (29,-1), (91,-3), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (64,3), (31,-1), (60,1), (27,-3), (56,1), (36,-1), (32,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1)], 7⟩]⟩

lemma phiCertifiedSegment66_checked : phiCertifiedSegment66.check=true := by decide +kernel

def phiCertifiedSegment67 : PhiCertifiedSegment :=
  ⟨(8/33), (9/37), 8, [
    ⟨8, 33, 9, 37, [(33,-1), (29,-1), (62,1), (58,1), (91,-3), (54,1), (38,-1), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (31,-1), (64,3), (27,-3), (60,1), (56,1), (36,-1), (32,-1), (61,1), (57,1), (53,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment67_checked : phiCertifiedSegment67.check=true := by decide +kernel

def phiCertifiedSegment68 : PhiCertifiedSegment :=
  ⟨(9/37), (23/91), 5, [
    ⟨9, 37, 13, 53, [(37,-1), (33,-1), (29,-1), (62,1), (58,1), (54,1), (91,-3), (38,-1), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (31,-1), (27,-3), (64,3), (60,1), (56,1), (36,-1), (32,-1), (61,1), (57,1), (53,1)], 5⟩,
    ⟨13, 53, 14, 57, [(53,1), (37,-1), (33,-1), (29,-1), (62,1), (58,1), (54,1), (38,-1), (91,-3), (34,-1), (30,-1), (59,1), (55,1), (35,-1), (31,-1), (27,-3), (64,3), (60,1), (56,1), (36,-1), (32,-1), (61,1), (57,1)], 5⟩,
    ⟨14, 57, 15, 61, [(57,1), (53,1), (37,-1), (33,-1), (29,-1), (62,1), (58,1), (54,1), (38,-1), (34,-1), (91,-3), (30,-1), (59,1), (55,1), (35,-1), (31,-1), (27,-3), (64,3), (60,1), (56,1), (36,-1), (32,-1), (61,1)], 5⟩,
    ⟨15, 61, 1, 4, [(61,1), (57,1), (53,1), (37,-1), (33,-1), (29,-1), (62,1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (91,-3), (59,1), (55,1), (35,-1), (31,-1), (27,-3), (64,3), (60,1), (56,1), (36,-1), (32,-1)], 5⟩,
    ⟨1, 4, 23, 91, [(32,-1), (36,-1), (56,1), (60,1), (64,3), (29,-1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (62,1), (27,-3), (31,-1), (35,-1), (55,1), (59,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment68_checked : phiCertifiedSegment68.check=true := by decide +kernel

def phiCertifiedSegment69 : PhiCertifiedSegment :=
  ⟨(23/91), (9/35), 6, [
    ⟨23, 91, 15, 59, [(91,-3), (32,-1), (36,-1), (56,1), (60,1), (64,3), (29,-1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (62,1), (27,-3), (31,-1), (35,-1), (55,1), (59,1)], 6⟩,
    ⟨15, 59, 14, 55, [(59,1), (32,-1), (91,-3), (36,-1), (56,1), (60,1), (64,3), (29,-1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (62,1), (27,-3), (31,-1), (35,-1), (55,1)], 6⟩,
    ⟨14, 55, 9, 35, [(55,1), (59,1), (32,-1), (36,-1), (91,-3), (56,1), (60,1), (64,3), (29,-1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (62,1), (27,-3), (31,-1), (35,-1)], 6⟩]⟩

lemma phiCertifiedSegment69_checked : phiCertifiedSegment69.check=true := by decide +kernel

def phiCertifiedSegment70 : PhiCertifiedSegment :=
  ⟨(9/35), (7/27), 7, [
    ⟨9, 35, 8, 31, [(35,-1), (55,1), (59,1), (32,-1), (36,-1), (56,1), (91,-3), (60,1), (29,-1), (64,3), (33,-1), (37,-1), (53,1), (57,1), (61,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (27,-3), (62,1), (31,-1)], 7⟩,
    ⟨8, 31, 15, 58, [(31,-1), (62,1), (35,-1), (55,1), (59,1), (32,-1), (36,-1), (56,1), (29,-1), (60,1), (91,-3), (33,-1), (64,3), (37,-1), (53,1), (57,1), (30,-1), (61,1), (34,-1), (38,-1), (54,1), (27,-3), (58,1)], 7⟩,
    ⟨15, 58, 7, 27, [(58,1), (31,-1), (62,1), (35,-1), (55,1), (59,1), (32,-1), (36,-1), (56,1), (29,-1), (60,1), (33,-1), (91,-3), (64,3), (37,-1), (53,1), (57,1), (30,-1), (61,1), (34,-1), (38,-1), (54,1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment70_checked : phiCertifiedSegment70.check=true := by decide +kernel

def phiCertifiedSegment71 : PhiCertifiedSegment :=
  ⟨(7/27), (4/15), 4, [
    ⟨7, 27, 6, 23, [(27,-3), (54,1), (31,-1), (58,1), (35,-1), (62,1), (55,1), (32,-1), (59,1), (36,-1), (29,-1), (56,1), (33,-1), (60,1), (37,-1), (64,3), (91,-3), (53,1), (30,-1), (57,1), (34,-1), (61,1), (38,-1)], 4⟩,
    ⟨6, 23, 16, 61, [(27,-3), (31,-1), (54,1), (35,-1), (58,1), (62,1), (32,-1), (55,1), (36,-1), (59,1), (29,-1), (33,-1), (56,1), (37,-1), (60,1), (64,3), (91,-3), (30,-1), (53,1), (34,-1), (57,1), (38,-1), (61,1)], 4⟩,
    ⟨16, 61, 5, 19, [(61,1), (27,-3), (31,-1), (54,1), (35,-1), (58,1), (62,1), (32,-1), (55,1), (36,-1), (59,1), (29,-1), (33,-1), (56,1), (37,-1), (60,1), (64,3), (30,-1), (91,-3), (53,1), (34,-1), (57,1), (38,-1)], 4⟩,
    ⟨5, 19, 24, 91, [(38,-1), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1), (53,1), (91,-3)], 4⟩,
    ⟨24, 91, 14, 53, [(91,-3), (38,-1), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1), (53,1)], 4⟩,
    ⟨14, 53, 9, 34, [(53,1), (38,-1), (91,-3), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1)], 4⟩,
    ⟨9, 34, 17, 64, [(34,-1), (53,1), (38,-1), (57,1), (91,-3), (27,-3), (61,1), (31,-1), (35,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (56,1), (60,1), (30,-1), (64,3)], 4⟩,
    ⟨17, 64, 4, 15, [(64,3), (34,-1), (53,1), (38,-1), (57,1), (27,-3), (91,-3), (61,1), (31,-1), (35,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (56,1), (60,1), (30,-1)], 4⟩]⟩

lemma phiCertifiedSegment71_checked : phiCertifiedSegment71.check=true := by decide +kernel

def phiCertifiedSegment72 : PhiCertifiedSegment :=
  ⟨(4/15), (10/37), 5, [
    ⟨4, 15, 15, 56, [(30,-1), (60,1), (34,-1), (64,3), (38,-1), (53,1), (27,-3), (57,1), (31,-1), (61,1), (91,-3), (35,-1), (54,1), (58,1), (32,-1), (62,1), (36,-1), (55,1), (29,-1), (59,1), (33,-1), (37,-1), (56,1)], 5⟩,
    ⟨15, 56, 7, 26, [(56,1), (30,-1), (60,1), (34,-1), (64,3), (38,-1), (53,1), (27,-3), (57,1), (31,-1), (61,1), (35,-1), (91,-3), (54,1), (58,1), (32,-1), (62,1), (36,-1), (55,1), (29,-1), (59,1), (33,-1), (37,-1)], 5⟩,
    ⟨7, 26, 10, 37, [(30,-1), (56,1), (34,-1), (60,1), (38,-1), (64,3), (27,-3), (53,1), (31,-1), (57,1), (35,-1), (61,1), (91,-3), (54,1), (32,-1), (58,1), (36,-1), (62,1), (29,-1), (55,1), (33,-1), (59,1), (37,-1)], 5⟩]⟩

lemma phiCertifiedSegment72_checked : phiCertifiedSegment72.check=true := by decide +kernel

def phiCertifiedSegment73 : PhiCertifiedSegment :=
  ⟨(10/37), (2/7), 4, [
    ⟨10, 37, 16, 59, [(37,-1), (30,-1), (56,1), (34,-1), (60,1), (38,-1), (27,-3), (64,3), (53,1), (31,-1), (57,1), (35,-1), (61,1), (54,1), (91,-3), (32,-1), (58,1), (36,-1), (62,1), (29,-1), (55,1), (33,-1), (59,1)], 4⟩,
    ⟨16, 59, 3, 11, [(59,1), (37,-1), (30,-1), (56,1), (34,-1), (60,1), (38,-1), (27,-3), (64,3), (53,1), (31,-1), (57,1), (35,-1), (61,1), (54,1), (32,-1), (91,-3), (58,1), (36,-1), (62,1), (29,-1), (55,1), (33,-1)], 4⟩,
    ⟨3, 11, 17, 62, [(33,-1), (55,1), (37,-1), (59,1), (30,-1), (34,-1), (56,1), (27,-3), (38,-1), (60,1), (31,-1), (53,1), (64,3), (35,-1), (57,1), (61,1), (32,-1), (54,1), (36,-1), (58,1), (91,-3), (29,-1), (62,1)], 4⟩,
    ⟨17, 62, 25, 91, [(62,1), (33,-1), (55,1), (37,-1), (59,1), (30,-1), (34,-1), (56,1), (27,-3), (38,-1), (60,1), (31,-1), (53,1), (64,3), (35,-1), (57,1), (61,1), (32,-1), (54,1), (36,-1), (58,1), (29,-1), (91,-3)], 4⟩,
    ⟨25, 91, 8, 29, [(91,-3), (62,1), (33,-1), (55,1), (37,-1), (59,1), (30,-1), (34,-1), (56,1), (27,-3), (38,-1), (60,1), (31,-1), (53,1), (64,3), (35,-1), (57,1), (61,1), (32,-1), (54,1), (36,-1), (58,1), (29,-1)], 4⟩,
    ⟨8, 29, 5, 18, [(29,-1), (58,1), (33,-1), (62,1), (91,-3), (55,1), (37,-1), (30,-1), (59,1), (34,-1), (27,-3), (56,1), (38,-1), (31,-1), (60,1), (53,1), (35,-1), (64,3), (57,1), (32,-1), (61,1), (54,1), (36,-1)], 4⟩,
    ⟨5, 18, 17, 61, [(36,-1), (54,1), (29,-1), (58,1), (33,-1), (62,1), (37,-1), (55,1), (91,-3), (30,-1), (59,1), (34,-1), (27,-3), (38,-1), (56,1), (31,-1), (60,1), (35,-1), (53,1), (64,3), (57,1), (32,-1), (61,1)], 4⟩,
    ⟨17, 61, 7, 25, [(61,1), (36,-1), (54,1), (29,-1), (58,1), (33,-1), (62,1), (37,-1), (55,1), (30,-1), (91,-3), (59,1), (34,-1), (27,-3), (38,-1), (56,1), (31,-1), (60,1), (35,-1), (53,1), (64,3), (57,1), (32,-1)], 4⟩,
    ⟨7, 25, 16, 57, [(36,-1), (61,1), (29,-1), (54,1), (33,-1), (58,1), (37,-1), (62,1), (30,-1), (55,1), (91,-3), (34,-1), (59,1), (27,-3), (38,-1), (31,-1), (56,1), (35,-1), (60,1), (53,1), (64,3), (32,-1), (57,1)], 4⟩,
    ⟨16, 57, 9, 32, [(57,1), (36,-1), (61,1), (29,-1), (54,1), (33,-1), (58,1), (37,-1), (62,1), (30,-1), (55,1), (34,-1), (91,-3), (59,1), (27,-3), (38,-1), (31,-1), (56,1), (35,-1), (60,1), (53,1), (64,3), (32,-1)], 4⟩,
    ⟨9, 32, 15, 53, [(32,-1), (64,3), (57,1), (36,-1), (29,-1), (61,1), (54,1), (33,-1), (58,1), (37,-1), (30,-1), (62,1), (55,1), (34,-1), (27,-3), (59,1), (91,-3), (38,-1), (31,-1), (56,1), (35,-1), (60,1), (53,1)], 4⟩,
    ⟨15, 53, 17, 60, [(53,1), (32,-1), (64,3), (57,1), (36,-1), (29,-1), (61,1), (54,1), (33,-1), (58,1), (37,-1), (30,-1), (62,1), (55,1), (34,-1), (27,-3), (59,1), (38,-1), (91,-3), (31,-1), (56,1), (35,-1), (60,1)], 4⟩,
    ⟨17, 60, 2, 7, [(60,1), (53,1), (32,-1), (64,3), (57,1), (36,-1), (29,-1), (61,1), (54,1), (33,-1), (58,1), (37,-1), (30,-1), (62,1), (55,1), (34,-1), (27,-3), (59,1), (38,-1), (31,-1), (91,-3), (56,1), (35,-1)], 4⟩]⟩

lemma phiCertifiedSegment73_checked : phiCertifiedSegment73.check=true := by decide +kernel

def phiCertifiedSegment74 : PhiCertifiedSegment :=
  ⟨(2/7), (9/31), 7, [
    ⟨2, 7, 17, 59, [(35,-1), (56,1), (91,-3), (32,-1), (53,1), (60,1), (29,-1), (36,-1), (57,1), (64,3), (33,-1), (54,1), (61,1), (30,-1), (37,-1), (58,1), (27,-3), (34,-1), (55,1), (62,1), (31,-1), (38,-1), (59,1)], 7⟩,
    ⟨17, 59, 11, 38, [(59,1), (35,-1), (56,1), (32,-1), (91,-3), (53,1), (60,1), (29,-1), (36,-1), (57,1), (64,3), (33,-1), (54,1), (61,1), (30,-1), (37,-1), (58,1), (27,-3), (34,-1), (55,1), (62,1), (31,-1), (38,-1)], 7⟩,
    ⟨11, 38, 9, 31, [(38,-1), (59,1), (35,-1), (56,1), (32,-1), (53,1), (91,-3), (60,1), (29,-1), (36,-1), (57,1), (64,3), (33,-1), (54,1), (61,1), (30,-1), (37,-1), (58,1), (27,-3), (34,-1), (55,1), (62,1), (31,-1)], 7⟩]⟩

lemma phiCertifiedSegment74_checked : phiCertifiedSegment74.check=true := by decide +kernel

def phiCertifiedSegment75 : PhiCertifiedSegment :=
  ⟨(9/31), (7/24), 8, [
    ⟨9, 31, 16, 55, [(31,-1), (62,1), (38,-1), (59,1), (35,-1), (56,1), (32,-1), (53,1), (29,-1), (60,1), (91,-3), (36,-1), (57,1), (33,-1), (64,3), (54,1), (30,-1), (61,1), (37,-1), (27,-3), (58,1), (34,-1), (55,1)], 8⟩,
    ⟨16, 55, 7, 24, [(55,1), (31,-1), (62,1), (38,-1), (59,1), (35,-1), (56,1), (32,-1), (53,1), (29,-1), (60,1), (36,-1), (91,-3), (57,1), (33,-1), (64,3), (54,1), (30,-1), (61,1), (37,-1), (27,-3), (58,1), (34,-1)], 8⟩]⟩

lemma phiCertifiedSegment75_checked : phiCertifiedSegment75.check=true := by decide +kernel

def phiCertifiedSegment76 : PhiCertifiedSegment :=
  ⟨(7/24), (5/17), 7, [
    ⟨7, 24, 17, 58, [(31,-1), (55,1), (38,-1), (62,1), (35,-1), (59,1), (32,-1), (56,1), (29,-1), (53,1), (36,-1), (60,1), (91,-3), (33,-1), (57,1), (64,3), (30,-1), (54,1), (37,-1), (61,1), (27,-3), (34,-1), (58,1)], 7⟩,
    ⟨17, 58, 5, 17, [(58,1), (31,-1), (55,1), (38,-1), (62,1), (35,-1), (59,1), (32,-1), (56,1), (29,-1), (53,1), (36,-1), (60,1), (33,-1), (91,-3), (57,1), (64,3), (30,-1), (54,1), (37,-1), (61,1), (27,-3), (34,-1)], 7⟩]⟩

lemma phiCertifiedSegment76_checked : phiCertifiedSegment76.check=true := by decide +kernel

def phiCertifiedSegment77 : PhiCertifiedSegment :=
  ⟨(5/17), (8/27), 8, [
    ⟨5, 17, 18, 61, [(34,-1), (58,1), (31,-1), (38,-1), (55,1), (62,1), (35,-1), (59,1), (32,-1), (56,1), (29,-1), (36,-1), (53,1), (60,1), (33,-1), (57,1), (91,-3), (30,-1), (64,3), (37,-1), (54,1), (27,-3), (61,1)], 8⟩,
    ⟨18, 61, 8, 27, [(61,1), (34,-1), (58,1), (31,-1), (38,-1), (55,1), (62,1), (35,-1), (59,1), (32,-1), (56,1), (29,-1), (36,-1), (53,1), (60,1), (33,-1), (57,1), (30,-1), (91,-3), (64,3), (37,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment77_checked : phiCertifiedSegment77.check=true := by decide +kernel

def phiCertifiedSegment78 : PhiCertifiedSegment :=
  ⟨(8/27), (3/10), 5, [
    ⟨8, 27, 27, 91, [(27,-3), (54,1), (34,-1), (61,1), (31,-1), (58,1), (38,-1), (55,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (36,-1), (53,1), (33,-1), (60,1), (30,-1), (57,1), (37,-1), (64,3), (91,-3)], 5⟩,
    ⟨27, 91, 19, 64, [(91,-3), (27,-3), (54,1), (34,-1), (61,1), (31,-1), (58,1), (38,-1), (55,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (36,-1), (53,1), (33,-1), (60,1), (30,-1), (57,1), (37,-1), (64,3)], 5⟩,
    ⟨19, 64, 11, 37, [(64,3), (27,-3), (91,-3), (54,1), (34,-1), (61,1), (31,-1), (58,1), (38,-1), (55,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (36,-1), (53,1), (33,-1), (60,1), (30,-1), (57,1), (37,-1)], 5⟩,
    ⟨11, 37, 17, 57, [(37,-1), (27,-3), (64,3), (54,1), (91,-3), (34,-1), (61,1), (31,-1), (58,1), (38,-1), (55,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (36,-1), (53,1), (33,-1), (60,1), (30,-1), (57,1)], 5⟩,
    ⟨17, 57, 3, 10, [(57,1), (37,-1), (27,-3), (64,3), (54,1), (34,-1), (91,-3), (61,1), (31,-1), (58,1), (38,-1), (55,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (36,-1), (53,1), (33,-1), (60,1), (30,-1)], 5⟩]⟩

lemma phiCertifiedSegment78_checked : phiCertifiedSegment78.check=true := by decide +kernel

def phiCertifiedSegment79 : PhiCertifiedSegment :=
  ⟨(3/10), (7/23), 4, [
    ⟨3, 10, 16, 53, [(30,-1), (60,1), (27,-3), (37,-1), (57,1), (34,-1), (54,1), (64,3), (31,-1), (61,1), (91,-3), (38,-1), (58,1), (35,-1), (55,1), (32,-1), (62,1), (29,-1), (59,1), (36,-1), (56,1), (33,-1), (53,1)], 4⟩,
    ⟨16, 53, 10, 33, [(53,1), (30,-1), (60,1), (27,-3), (37,-1), (57,1), (34,-1), (54,1), (64,3), (31,-1), (61,1), (38,-1), (91,-3), (58,1), (35,-1), (55,1), (32,-1), (62,1), (29,-1), (59,1), (36,-1), (56,1), (33,-1)], 4⟩,
    ⟨10, 33, 17, 56, [(33,-1), (53,1), (30,-1), (27,-3), (60,1), (37,-1), (57,1), (34,-1), (54,1), (31,-1), (64,3), (61,1), (38,-1), (58,1), (91,-3), (35,-1), (55,1), (32,-1), (29,-1), (62,1), (59,1), (36,-1), (56,1)], 4⟩,
    ⟨17, 56, 7, 23, [(56,1), (33,-1), (53,1), (30,-1), (27,-3), (60,1), (37,-1), (57,1), (34,-1), (54,1), (31,-1), (64,3), (61,1), (38,-1), (58,1), (35,-1), (91,-3), (55,1), (32,-1), (29,-1), (62,1), (59,1), (36,-1)], 4⟩]⟩

lemma phiCertifiedSegment79_checked : phiCertifiedSegment79.check=true := by decide +kernel

def phiCertifiedSegment80 : PhiCertifiedSegment :=
  ⟨(7/23), (4/13), 5, [
    ⟨7, 23, 18, 59, [(33,-1), (56,1), (30,-1), (53,1), (27,-3), (37,-1), (60,1), (34,-1), (57,1), (31,-1), (54,1), (64,3), (38,-1), (61,1), (35,-1), (58,1), (91,-3), (32,-1), (55,1), (29,-1), (62,1), (36,-1), (59,1)], 5⟩,
    ⟨18, 59, 11, 36, [(59,1), (33,-1), (56,1), (30,-1), (53,1), (27,-3), (37,-1), (60,1), (34,-1), (57,1), (31,-1), (54,1), (64,3), (38,-1), (61,1), (35,-1), (58,1), (32,-1), (91,-3), (55,1), (29,-1), (62,1), (36,-1)], 5⟩,
    ⟨11, 36, 19, 62, [(36,-1), (59,1), (33,-1), (56,1), (30,-1), (53,1), (27,-3), (37,-1), (60,1), (34,-1), (57,1), (31,-1), (54,1), (64,3), (38,-1), (61,1), (35,-1), (58,1), (32,-1), (55,1), (91,-3), (29,-1), (62,1)], 5⟩,
    ⟨19, 62, 4, 13, [(62,1), (36,-1), (59,1), (33,-1), (56,1), (30,-1), (53,1), (27,-3), (37,-1), (60,1), (34,-1), (57,1), (31,-1), (54,1), (64,3), (38,-1), (61,1), (35,-1), (58,1), (32,-1), (55,1), (29,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment80_checked : phiCertifiedSegment80.check=true := by decide +kernel

def phiCertifiedSegment81 : PhiCertifiedSegment :=
  ⟨(4/13), (6/19), 4, [
    ⟨4, 13, 17, 55, [(91,-3), (36,-1), (62,1), (33,-1), (59,1), (30,-1), (56,1), (27,-3), (53,1), (37,-1), (34,-1), (60,1), (31,-1), (57,1), (54,1), (38,-1), (64,3), (35,-1), (61,1), (32,-1), (58,1), (29,-1), (55,1)], 4⟩,
    ⟨17, 55, 9, 29, [(55,1), (36,-1), (91,-3), (62,1), (33,-1), (59,1), (30,-1), (56,1), (27,-3), (53,1), (37,-1), (34,-1), (60,1), (31,-1), (57,1), (54,1), (38,-1), (64,3), (35,-1), (61,1), (32,-1), (58,1), (29,-1)], 4⟩,
    ⟨9, 29, 19, 61, [(29,-1), (58,1), (55,1), (36,-1), (33,-1), (62,1), (91,-3), (30,-1), (59,1), (27,-3), (56,1), (53,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (38,-1), (35,-1), (64,3), (32,-1), (61,1)], 4⟩,
    ⟨19, 61, 5, 16, [(61,1), (29,-1), (58,1), (55,1), (36,-1), (33,-1), (62,1), (30,-1), (91,-3), (59,1), (27,-3), (56,1), (53,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (38,-1), (35,-1), (64,3), (32,-1)], 4⟩,
    ⟨5, 16, 11, 35, [(32,-1), (64,3), (29,-1), (61,1), (58,1), (55,1), (36,-1), (33,-1), (30,-1), (62,1), (27,-3), (59,1), (91,-3), (56,1), (37,-1), (53,1), (34,-1), (31,-1), (60,1), (57,1), (38,-1), (54,1), (35,-1)], 4⟩,
    ⟨11, 35, 17, 54, [(35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1), (91,-3), (37,-1), (53,1), (34,-1), (31,-1), (60,1), (57,1), (38,-1), (54,1)], 4⟩,
    ⟨17, 54, 6, 19, [(54,1), (35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1), (37,-1), (91,-3), (53,1), (34,-1), (31,-1), (60,1), (57,1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment81_checked : phiCertifiedSegment81.check=true := by decide +kernel

def phiCertifiedSegment82 : PhiCertifiedSegment :=
  ⟨(6/19), (29/91), 5, [
    ⟨6, 19, 19, 60, [(38,-1), (57,1), (35,-1), (54,1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (36,-1), (55,1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (37,-1), (56,1), (34,-1), (53,1), (91,-3), (31,-1), (60,1)], 5⟩,
    ⟨19, 60, 7, 22, [(60,1), (38,-1), (57,1), (35,-1), (54,1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (36,-1), (55,1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (37,-1), (56,1), (34,-1), (53,1), (31,-1), (91,-3)], 5⟩,
    ⟨7, 22, 29, 91, [(38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (64,3), (61,1), (36,-1), (58,1), (33,-1), (55,1), (30,-1), (27,-3), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment82_checked : phiCertifiedSegment82.check=true := by decide +kernel

def phiCertifiedSegment83 : PhiCertifiedSegment :=
  ⟨(29/91), (9/28), 7, [
    ⟨29, 91, 8, 25, [(91,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (64,3), (61,1), (36,-1), (58,1), (33,-1), (55,1), (30,-1), (27,-3), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1)], 7⟩,
    ⟨8, 25, 17, 53, [(91,-3), (38,-1), (35,-1), (60,1), (32,-1), (57,1), (29,-1), (54,1), (64,3), (36,-1), (61,1), (33,-1), (58,1), (30,-1), (55,1), (27,-3), (37,-1), (62,1), (34,-1), (59,1), (31,-1), (56,1), (53,1)], 7⟩,
    ⟨17, 53, 9, 28, [(53,1), (38,-1), (91,-3), (35,-1), (60,1), (32,-1), (57,1), (29,-1), (54,1), (64,3), (36,-1), (61,1), (33,-1), (58,1), (30,-1), (55,1), (27,-3), (37,-1), (62,1), (34,-1), (59,1), (31,-1), (56,1)], 7⟩]⟩

lemma phiCertifiedSegment83_checked : phiCertifiedSegment83.check=true := by decide +kernel

def phiCertifiedSegment84 : PhiCertifiedSegment :=
  ⟨(9/28), (10/31), 6, [
    ⟨9, 28, 19, 59, [(56,1), (53,1), (38,-1), (35,-1), (91,-3), (32,-1), (60,1), (29,-1), (57,1), (54,1), (36,-1), (64,3), (33,-1), (61,1), (30,-1), (58,1), (27,-3), (55,1), (37,-1), (34,-1), (62,1), (31,-1), (59,1)], 6⟩,
    ⟨19, 59, 10, 31, [(59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (91,-3), (60,1), (29,-1), (57,1), (54,1), (36,-1), (64,3), (33,-1), (61,1), (30,-1), (58,1), (27,-3), (55,1), (37,-1), (34,-1), (62,1), (31,-1)], 6⟩]⟩

lemma phiCertifiedSegment84_checked : phiCertifiedSegment84.check=true := by decide +kernel

def phiCertifiedSegment85 : PhiCertifiedSegment :=
  ⟨(10/31), (11/34), 7, [
    ⟨10, 31, 11, 34, [(31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (91,-3), (57,1), (54,1), (36,-1), (33,-1), (64,3), (30,-1), (61,1), (27,-3), (58,1), (55,1), (37,-1), (34,-1)], 7⟩]⟩

lemma phiCertifiedSegment85_checked : phiCertifiedSegment85.check=true := by decide +kernel

def phiCertifiedSegment86 : PhiCertifiedSegment :=
  ⟨(11/34), (12/37), 6, [
    ⟨11, 34, 12, 37, [(34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (91,-3), (54,1), (36,-1), (33,-1), (30,-1), (64,3), (27,-3), (61,1), (58,1), (55,1), (37,-1)], 6⟩]⟩

lemma phiCertifiedSegment86_checked : phiCertifiedSegment86.check=true := by decide +kernel

def phiCertifiedSegment87 : PhiCertifiedSegment :=
  ⟨(12/37), (30/91), 3, [
    ⟨12, 37, 18, 55, [(37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (91,-3), (36,-1), (33,-1), (30,-1), (27,-3), (64,3), (61,1), (58,1), (55,1)], 3⟩,
    ⟨18, 55, 19, 58, [(55,1), (37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (36,-1), (91,-3), (33,-1), (30,-1), (27,-3), (64,3), (61,1), (58,1)], 3⟩,
    ⟨19, 58, 20, 61, [(58,1), (55,1), (37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (91,-3), (30,-1), (27,-3), (64,3), (61,1)], 3⟩,
    ⟨20, 61, 21, 64, [(61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (91,-3), (27,-3), (64,3)], 3⟩,
    ⟨21, 64, 30, 91, [(64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (91,-3)], 3⟩]⟩

lemma phiCertifiedSegment87_checked : phiCertifiedSegment87.check=true := by decide +kernel

def phiCertifiedSegment88 : PhiCertifiedSegment :=
  ⟨(30/91), (1/3), 6, [
    ⟨30, 91, 1, 3, [(91,-3), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3)], 6⟩]⟩

lemma phiCertifiedSegment88_checked : phiCertifiedSegment88.check=true := by decide +kernel

def phiCertifiedSegment89 : PhiCertifiedSegment :=
  ⟨(1/3), (31/91), 3, [
    ⟨1, 3, 21, 62, [(27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (91,-3), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1)], 3⟩,
    ⟨21, 62, 20, 59, [(62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (91,-3), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1)], 3⟩,
    ⟨20, 59, 19, 56, [(59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (91,-3), (35,-1), (38,-1), (53,1), (56,1)], 3⟩,
    ⟨19, 56, 18, 53, [(56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1), (91,-3), (38,-1), (53,1)], 3⟩,
    ⟨18, 53, 31, 91, [(53,1), (56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1), (38,-1), (91,-3)], 3⟩]⟩

lemma phiCertifiedSegment89_checked : phiCertifiedSegment89.check=true := by decide +kernel

def phiCertifiedSegment90 : PhiCertifiedSegment :=
  ⟨(31/91), (10/29), 4, [
    ⟨31, 91, 13, 38, [(91,-3), (53,1), (56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1), (38,-1)], 4⟩,
    ⟨13, 38, 12, 35, [(38,-1), (53,1), (91,-3), (56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1)], 4⟩,
    ⟨12, 35, 11, 32, [(35,-1), (38,-1), (53,1), (56,1), (91,-3), (59,1), (27,-3), (62,1), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (29,-1), (64,3), (32,-1)], 4⟩,
    ⟨11, 32, 21, 61, [(32,-1), (64,3), (35,-1), (38,-1), (53,1), (56,1), (27,-3), (59,1), (91,-3), (30,-1), (62,1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (29,-1), (61,1)], 4⟩,
    ⟨21, 61, 10, 29, [(61,1), (32,-1), (64,3), (35,-1), (38,-1), (53,1), (56,1), (27,-3), (59,1), (30,-1), (91,-3), (62,1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment90_checked : phiCertifiedSegment90.check=true := by decide +kernel

def phiCertifiedSegment91 : PhiCertifiedSegment :=
  ⟨(10/29), (7/20), 5, [
    ⟨10, 29, 19, 55, [(29,-1), (58,1), (32,-1), (61,1), (35,-1), (64,3), (38,-1), (53,1), (27,-3), (56,1), (30,-1), (59,1), (33,-1), (62,1), (91,-3), (36,-1), (54,1), (57,1), (31,-1), (60,1), (34,-1), (37,-1), (55,1)], 5⟩,
    ⟨19, 55, 9, 26, [(55,1), (29,-1), (58,1), (32,-1), (61,1), (35,-1), (64,3), (38,-1), (53,1), (27,-3), (56,1), (30,-1), (59,1), (33,-1), (62,1), (36,-1), (91,-3), (54,1), (57,1), (31,-1), (60,1), (34,-1), (37,-1)], 5⟩,
    ⟨9, 26, 8, 23, [(29,-1), (55,1), (32,-1), (58,1), (35,-1), (61,1), (38,-1), (64,3), (27,-3), (53,1), (30,-1), (56,1), (33,-1), (59,1), (36,-1), (62,1), (91,-3), (54,1), (31,-1), (57,1), (34,-1), (60,1), (37,-1)], 5⟩,
    ⟨8, 23, 7, 20, [(29,-1), (32,-1), (55,1), (35,-1), (58,1), (38,-1), (61,1), (64,3), (27,-3), (30,-1), (53,1), (33,-1), (56,1), (36,-1), (59,1), (62,1), (91,-3), (31,-1), (54,1), (34,-1), (57,1), (37,-1), (60,1)], 5⟩]⟩

lemma phiCertifiedSegment91_checked : phiCertifiedSegment91.check=true := by decide +kernel

def phiCertifiedSegment92 : PhiCertifiedSegment :=
  ⟨(7/20), (13/37), 4, [
    ⟨7, 20, 20, 57, [(60,1), (29,-1), (32,-1), (35,-1), (55,1), (38,-1), (58,1), (61,1), (64,3), (27,-3), (30,-1), (33,-1), (53,1), (36,-1), (56,1), (59,1), (62,1), (31,-1), (91,-3), (34,-1), (54,1), (37,-1), (57,1)], 4⟩,
    ⟨20, 57, 13, 37, [(57,1), (60,1), (29,-1), (32,-1), (35,-1), (55,1), (38,-1), (58,1), (61,1), (64,3), (27,-3), (30,-1), (33,-1), (53,1), (36,-1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (91,-3), (54,1), (37,-1)], 4⟩]⟩

lemma phiCertifiedSegment92_checked : phiCertifiedSegment92.check=true := by decide +kernel

def phiCertifiedSegment93 : PhiCertifiedSegment :=
  ⟨(13/37), (5/14), 5, [
    ⟨13, 37, 32, 91, [(37,-1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (55,1), (38,-1), (58,1), (61,1), (27,-3), (64,3), (30,-1), (33,-1), (53,1), (36,-1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (54,1), (91,-3)], 5⟩,
    ⟨32, 91, 19, 54, [(91,-3), (37,-1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (55,1), (38,-1), (58,1), (61,1), (27,-3), (64,3), (30,-1), (33,-1), (53,1), (36,-1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (54,1)], 5⟩,
    ⟨19, 54, 6, 17, [(54,1), (37,-1), (91,-3), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (55,1), (38,-1), (58,1), (61,1), (27,-3), (64,3), (30,-1), (33,-1), (53,1), (36,-1), (56,1), (59,1), (62,1), (31,-1), (34,-1)], 5⟩,
    ⟨6, 17, 11, 31, [(34,-1), (37,-1), (54,1), (57,1), (91,-3), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (55,1), (58,1), (27,-3), (61,1), (30,-1), (64,3), (33,-1), (36,-1), (53,1), (56,1), (59,1), (62,1), (31,-1)], 5⟩,
    ⟨11, 31, 21, 59, [(31,-1), (62,1), (34,-1), (37,-1), (54,1), (57,1), (29,-1), (60,1), (91,-3), (32,-1), (35,-1), (38,-1), (55,1), (27,-3), (58,1), (30,-1), (61,1), (33,-1), (64,3), (36,-1), (53,1), (56,1), (59,1)], 5⟩,
    ⟨21, 59, 5, 14, [(59,1), (31,-1), (62,1), (34,-1), (37,-1), (54,1), (57,1), (29,-1), (60,1), (32,-1), (91,-3), (35,-1), (38,-1), (55,1), (27,-3), (58,1), (30,-1), (61,1), (33,-1), (64,3), (36,-1), (53,1), (56,1)], 5⟩]⟩

lemma phiCertifiedSegment93_checked : phiCertifiedSegment93.check=true := by decide +kernel

def phiCertifiedSegment94 : PhiCertifiedSegment :=
  ⟨(5/14), (33/91), 4, [
    ⟨5, 14, 19, 53, [(56,1), (31,-1), (59,1), (34,-1), (62,1), (37,-1), (54,1), (29,-1), (57,1), (32,-1), (60,1), (35,-1), (91,-3), (38,-1), (27,-3), (55,1), (30,-1), (58,1), (33,-1), (61,1), (36,-1), (64,3), (53,1)], 4⟩,
    ⟨19, 53, 23, 64, [(53,1), (56,1), (31,-1), (59,1), (34,-1), (62,1), (37,-1), (54,1), (29,-1), (57,1), (32,-1), (60,1), (35,-1), (38,-1), (91,-3), (27,-3), (55,1), (30,-1), (58,1), (33,-1), (61,1), (36,-1), (64,3)], 4⟩,
    ⟨23, 64, 9, 25, [(64,3), (53,1), (56,1), (31,-1), (59,1), (34,-1), (62,1), (37,-1), (54,1), (29,-1), (57,1), (32,-1), (60,1), (35,-1), (38,-1), (27,-3), (91,-3), (55,1), (30,-1), (58,1), (33,-1), (61,1), (36,-1)], 4⟩,
    ⟨9, 25, 22, 61, [(64,3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (27,-3), (91,-3), (30,-1), (55,1), (33,-1), (58,1), (36,-1), (61,1)], 4⟩,
    ⟨22, 61, 13, 36, [(61,1), (64,3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (27,-3), (30,-1), (91,-3), (55,1), (33,-1), (58,1), (36,-1)], 4⟩,
    ⟨13, 36, 21, 58, [(36,-1), (61,1), (64,3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (27,-3), (30,-1), (55,1), (91,-3), (33,-1), (58,1)], 4⟩,
    ⟨21, 58, 33, 91, [(58,1), (36,-1), (61,1), (64,3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (27,-3), (30,-1), (55,1), (33,-1), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment94_checked : phiCertifiedSegment94.check=true := by decide +kernel

def phiCertifiedSegment95 : PhiCertifiedSegment :=
  ⟨(33/91), (4/11), 7, [
    ⟨33, 91, 4, 11, [(91,-3), (58,1), (36,-1), (61,1), (64,3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (27,-3), (30,-1), (55,1), (33,-1)], 7⟩]⟩

lemma phiCertifiedSegment95_checked : phiCertifiedSegment95.check=true := by decide +kernel

def phiCertifiedSegment96 : PhiCertifiedSegment :=
  ⟨(4/11), (7/19), 8, [
    ⟨4, 11, 11, 30, [(33,-1), (55,1), (36,-1), (58,1), (91,-3), (61,1), (31,-1), (53,1), (64,3), (34,-1), (56,1), (37,-1), (59,1), (29,-1), (62,1), (32,-1), (54,1), (35,-1), (57,1), (27,-3), (38,-1), (60,1), (30,-1)], 8⟩,
    ⟨11, 30, 7, 19, [(30,-1), (60,1), (33,-1), (55,1), (36,-1), (58,1), (31,-1), (61,1), (91,-3), (53,1), (34,-1), (64,3), (56,1), (37,-1), (29,-1), (59,1), (32,-1), (62,1), (54,1), (35,-1), (27,-3), (57,1), (38,-1)], 8⟩]⟩

lemma phiCertifiedSegment96_checked : phiCertifiedSegment96.check=true := by decide +kernel

def phiCertifiedSegment97 : PhiCertifiedSegment :=
  ⟨(7/19), (10/27), 9, [
    ⟨7, 19, 10, 27, [(38,-1), (57,1), (30,-1), (60,1), (33,-1), (36,-1), (55,1), (58,1), (31,-1), (61,1), (34,-1), (53,1), (91,-3), (64,3), (37,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (54,1), (27,-3)], 9⟩]⟩

lemma phiCertifiedSegment97_checked : phiCertifiedSegment97.check=true := by decide +kernel

def phiCertifiedSegment98 : PhiCertifiedSegment :=
  ⟨(10/27), (3/8), 5, [
    ⟨10, 27, 23, 62, [(27,-3), (54,1), (38,-1), (30,-1), (57,1), (33,-1), (60,1), (36,-1), (55,1), (31,-1), (58,1), (34,-1), (61,1), (53,1), (37,-1), (64,3), (91,-3), (29,-1), (56,1), (32,-1), (59,1), (35,-1), (62,1)], 5⟩,
    ⟨23, 62, 13, 35, [(62,1), (27,-3), (54,1), (38,-1), (30,-1), (57,1), (33,-1), (60,1), (36,-1), (55,1), (31,-1), (58,1), (34,-1), (61,1), (53,1), (37,-1), (64,3), (29,-1), (91,-3), (56,1), (32,-1), (59,1), (35,-1)], 5⟩,
    ⟨13, 35, 22, 59, [(35,-1), (27,-3), (62,1), (54,1), (38,-1), (30,-1), (57,1), (33,-1), (60,1), (36,-1), (55,1), (31,-1), (58,1), (34,-1), (61,1), (53,1), (37,-1), (29,-1), (64,3), (56,1), (91,-3), (32,-1), (59,1)], 5⟩,
    ⟨22, 59, 34, 91, [(59,1), (35,-1), (27,-3), (62,1), (54,1), (38,-1), (30,-1), (57,1), (33,-1), (60,1), (36,-1), (55,1), (31,-1), (58,1), (34,-1), (61,1), (53,1), (37,-1), (29,-1), (64,3), (56,1), (32,-1), (91,-3)], 5⟩,
    ⟨34, 91, 3, 8, [(91,-3), (59,1), (35,-1), (27,-3), (62,1), (54,1), (38,-1), (30,-1), (57,1), (33,-1), (60,1), (36,-1), (55,1), (31,-1), (58,1), (34,-1), (61,1), (53,1), (37,-1), (29,-1), (64,3), (56,1), (32,-1)], 5⟩]⟩

lemma phiCertifiedSegment98_checked : phiCertifiedSegment98.check=true := by decide +kernel

def phiCertifiedSegment99 : PhiCertifiedSegment :=
  ⟨(3/8), (14/37), 3, [
    ⟨3, 8, 23, 61, [(32,-1), (56,1), (64,3), (27,-3), (35,-1), (59,1), (91,-3), (30,-1), (38,-1), (54,1), (62,1), (33,-1), (57,1), (36,-1), (60,1), (31,-1), (55,1), (34,-1), (58,1), (29,-1), (37,-1), (53,1), (61,1)], 3⟩,
    ⟨23, 61, 20, 53, [(61,1), (32,-1), (56,1), (64,3), (27,-3), (35,-1), (59,1), (30,-1), (91,-3), (38,-1), (54,1), (62,1), (33,-1), (57,1), (36,-1), (60,1), (31,-1), (55,1), (34,-1), (58,1), (29,-1), (37,-1), (53,1)], 3⟩,
    ⟨20, 53, 14, 37, [(53,1), (61,1), (32,-1), (56,1), (64,3), (27,-3), (35,-1), (59,1), (30,-1), (38,-1), (91,-3), (54,1), (62,1), (33,-1), (57,1), (36,-1), (60,1), (31,-1), (55,1), (34,-1), (58,1), (29,-1), (37,-1)], 3⟩]⟩

lemma phiCertifiedSegment99_checked : phiCertifiedSegment99.check=true := by decide +kernel

def phiCertifiedSegment100 : PhiCertifiedSegment :=
  ⟨(14/37), (8/21), 4, [
    ⟨14, 37, 11, 29, [(37,-1), (53,1), (61,1), (32,-1), (56,1), (27,-3), (64,3), (35,-1), (59,1), (30,-1), (38,-1), (54,1), (91,-3), (62,1), (33,-1), (57,1), (36,-1), (60,1), (31,-1), (55,1), (34,-1), (58,1), (29,-1)], 4⟩,
    ⟨11, 29, 8, 21, [(29,-1), (58,1), (37,-1), (53,1), (32,-1), (61,1), (27,-3), (56,1), (35,-1), (64,3), (30,-1), (59,1), (38,-1), (54,1), (33,-1), (62,1), (91,-3), (57,1), (36,-1), (31,-1), (60,1), (55,1), (34,-1)], 4⟩]⟩

lemma phiCertifiedSegment100_checked : phiCertifiedSegment100.check=true := by decide +kernel

def phiCertifiedSegment101 : PhiCertifiedSegment :=
  ⟨(8/21), (5/13), 5, [
    ⟨8, 21, 21, 55, [(29,-1), (37,-1), (58,1), (32,-1), (53,1), (61,1), (27,-3), (35,-1), (56,1), (64,3), (30,-1), (38,-1), (59,1), (33,-1), (54,1), (62,1), (91,-3), (36,-1), (57,1), (31,-1), (60,1), (34,-1), (55,1)], 5⟩,
    ⟨21, 55, 13, 34, [(55,1), (29,-1), (37,-1), (58,1), (32,-1), (53,1), (61,1), (27,-3), (35,-1), (56,1), (64,3), (30,-1), (38,-1), (59,1), (33,-1), (54,1), (62,1), (36,-1), (91,-3), (57,1), (31,-1), (60,1), (34,-1)], 5⟩,
    ⟨13, 34, 23, 60, [(34,-1), (55,1), (29,-1), (37,-1), (58,1), (32,-1), (53,1), (27,-3), (61,1), (35,-1), (56,1), (30,-1), (64,3), (38,-1), (59,1), (33,-1), (54,1), (62,1), (36,-1), (57,1), (91,-3), (31,-1), (60,1)], 5⟩,
    ⟨23, 60, 5, 13, [(60,1), (34,-1), (55,1), (29,-1), (37,-1), (58,1), (32,-1), (53,1), (27,-3), (61,1), (35,-1), (56,1), (30,-1), (64,3), (38,-1), (59,1), (33,-1), (54,1), (62,1), (36,-1), (57,1), (31,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment101_checked : phiCertifiedSegment101.check=true := by decide +kernel

def phiCertifiedSegment102 : PhiCertifiedSegment :=
  ⟨(5/13), (11/28), 4, [
    ⟨5, 13, 22, 57, [(91,-3), (34,-1), (60,1), (29,-1), (55,1), (37,-1), (32,-1), (58,1), (27,-3), (53,1), (35,-1), (61,1), (30,-1), (56,1), (38,-1), (64,3), (33,-1), (59,1), (54,1), (36,-1), (62,1), (31,-1), (57,1)], 4⟩,
    ⟨22, 57, 12, 31, [(57,1), (34,-1), (91,-3), (60,1), (29,-1), (55,1), (37,-1), (32,-1), (58,1), (27,-3), (53,1), (35,-1), (61,1), (30,-1), (56,1), (38,-1), (64,3), (33,-1), (59,1), (54,1), (36,-1), (62,1), (31,-1)], 4⟩,
    ⟨12, 31, 7, 18, [(31,-1), (62,1), (57,1), (34,-1), (29,-1), (60,1), (91,-3), (55,1), (37,-1), (32,-1), (27,-3), (58,1), (53,1), (35,-1), (30,-1), (61,1), (56,1), (38,-1), (33,-1), (64,3), (59,1), (54,1), (36,-1)], 4⟩,
    ⟨7, 18, 23, 59, [(36,-1), (54,1), (31,-1), (62,1), (57,1), (34,-1), (29,-1), (60,1), (37,-1), (55,1), (91,-3), (32,-1), (27,-3), (58,1), (35,-1), (53,1), (30,-1), (61,1), (38,-1), (56,1), (33,-1), (64,3), (59,1)], 4⟩,
    ⟨23, 59, 25, 64, [(59,1), (36,-1), (54,1), (31,-1), (62,1), (57,1), (34,-1), (29,-1), (60,1), (37,-1), (55,1), (32,-1), (91,-3), (27,-3), (58,1), (35,-1), (53,1), (30,-1), (61,1), (38,-1), (56,1), (33,-1), (64,3)], 4⟩,
    ⟨25, 64, 9, 23, [(64,3), (59,1), (36,-1), (54,1), (31,-1), (62,1), (57,1), (34,-1), (29,-1), (60,1), (37,-1), (55,1), (32,-1), (27,-3), (91,-3), (58,1), (35,-1), (53,1), (30,-1), (61,1), (38,-1), (56,1), (33,-1)], 4⟩,
    ⟨9, 23, 11, 28, [(64,3), (36,-1), (59,1), (31,-1), (54,1), (62,1), (34,-1), (57,1), (29,-1), (37,-1), (60,1), (32,-1), (55,1), (27,-3), (91,-3), (35,-1), (58,1), (30,-1), (53,1), (38,-1), (61,1), (33,-1), (56,1)], 4⟩]⟩

lemma phiCertifiedSegment102_checked : phiCertifiedSegment102.check=true := by decide +kernel

def phiCertifiedSegment103 : PhiCertifiedSegment :=
  ⟨(11/28), (13/33), 3, [
    ⟨11, 28, 24, 61, [(56,1), (36,-1), (64,3), (31,-1), (59,1), (54,1), (34,-1), (62,1), (29,-1), (57,1), (37,-1), (32,-1), (60,1), (27,-3), (55,1), (35,-1), (91,-3), (30,-1), (58,1), (53,1), (38,-1), (33,-1), (61,1)], 3⟩,
    ⟨24, 61, 13, 33, [(61,1), (56,1), (36,-1), (64,3), (31,-1), (59,1), (54,1), (34,-1), (62,1), (29,-1), (57,1), (37,-1), (32,-1), (60,1), (27,-3), (55,1), (35,-1), (30,-1), (91,-3), (58,1), (53,1), (38,-1), (33,-1)], 3⟩]⟩

lemma phiCertifiedSegment103_checked : phiCertifiedSegment103.check=true := by decide +kernel

def phiCertifiedSegment104 : PhiCertifiedSegment :=
  ⟨(13/33), (15/38), 5, [
    ⟨13, 33, 15, 38, [(33,-1), (61,1), (56,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (35,-1), (30,-1), (58,1), (91,-3), (53,1), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment104_checked : phiCertifiedSegment104.check=true := by decide +kernel

def phiCertifiedSegment105 : PhiCertifiedSegment :=
  ⟨(15/38), (36/91), 6, [
    ⟨15, 38, 36, 91, [(38,-1), (33,-1), (61,1), (56,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (35,-1), (30,-1), (58,1), (53,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment105_checked : phiCertifiedSegment105.check=true := by decide +kernel

def phiCertifiedSegment106 : PhiCertifiedSegment :=
  ⟨(36/91), (15/37), 7, [
    ⟨36, 91, 21, 53, [(91,-3), (38,-1), (33,-1), (61,1), (56,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (35,-1), (30,-1), (58,1), (53,1)], 7⟩,
    ⟨21, 53, 23, 58, [(53,1), (38,-1), (91,-3), (33,-1), (61,1), (56,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (35,-1), (30,-1), (58,1)], 7⟩,
    ⟨23, 58, 2, 5, [(58,1), (53,1), (38,-1), (33,-1), (91,-3), (61,1), (56,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (34,-1), (29,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (35,-1), (30,-1)], 7⟩,
    ⟨2, 5, 25, 62, [(30,-1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (61,1), (91,-3), (29,-1), (34,-1), (54,1), (59,1), (64,3), (27,-3), (32,-1), (37,-1), (57,1), (62,1)], 7⟩,
    ⟨25, 62, 23, 57, [(62,1), (30,-1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (61,1), (29,-1), (91,-3), (34,-1), (54,1), (59,1), (64,3), (27,-3), (32,-1), (37,-1), (57,1)], 7⟩,
    ⟨23, 57, 15, 37, [(57,1), (62,1), (30,-1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (61,1), (29,-1), (34,-1), (91,-3), (54,1), (59,1), (64,3), (27,-3), (32,-1), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment106_checked : phiCertifiedSegment106.check=true := by decide +kernel

def phiCertifiedSegment107 : PhiCertifiedSegment :=
  ⟨(15/37), (37/91), 6, [
    ⟨15, 37, 13, 32, [(37,-1), (57,1), (62,1), (30,-1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (61,1), (29,-1), (34,-1), (54,1), (91,-3), (59,1), (27,-3), (64,3), (32,-1)], 6⟩,
    ⟨13, 32, 37, 91, [(32,-1), (64,3), (37,-1), (57,1), (30,-1), (62,1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (29,-1), (61,1), (34,-1), (54,1), (27,-3), (59,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment107_checked : phiCertifiedSegment107.check=true := by decide +kernel

def phiCertifiedSegment108 : PhiCertifiedSegment :=
  ⟨(37/91), (11/27), 8, [
    ⟨37, 91, 24, 59, [(91,-3), (32,-1), (64,3), (37,-1), (57,1), (30,-1), (62,1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (29,-1), (61,1), (34,-1), (54,1), (27,-3), (59,1)], 8⟩,
    ⟨24, 59, 11, 27, [(59,1), (32,-1), (91,-3), (64,3), (37,-1), (57,1), (30,-1), (62,1), (35,-1), (55,1), (60,1), (33,-1), (38,-1), (53,1), (58,1), (31,-1), (36,-1), (56,1), (29,-1), (61,1), (34,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment108_checked : phiCertifiedSegment108.check=true := by decide +kernel

def phiCertifiedSegment109 : PhiCertifiedSegment :=
  ⟨(11/27), (9/22), 4, [
    ⟨11, 27, 9, 22, [(27,-3), (54,1), (32,-1), (59,1), (37,-1), (64,3), (91,-3), (30,-1), (57,1), (35,-1), (62,1), (55,1), (33,-1), (60,1), (38,-1), (53,1), (31,-1), (58,1), (36,-1), (29,-1), (56,1), (34,-1), (61,1)], 4⟩]⟩

lemma phiCertifiedSegment109_checked : phiCertifiedSegment109.check=true := by decide +kernel

def phiCertifiedSegment110 : PhiCertifiedSegment :=
  ⟨(9/22), (7/17), 3, [
    ⟨9, 22, 25, 61, [(27,-3), (32,-1), (54,1), (37,-1), (59,1), (64,3), (91,-3), (30,-1), (35,-1), (57,1), (62,1), (33,-1), (55,1), (38,-1), (60,1), (31,-1), (53,1), (36,-1), (58,1), (29,-1), (34,-1), (56,1), (61,1)], 3⟩,
    ⟨25, 61, 23, 56, [(61,1), (27,-3), (32,-1), (54,1), (37,-1), (59,1), (64,3), (30,-1), (91,-3), (35,-1), (57,1), (62,1), (33,-1), (55,1), (38,-1), (60,1), (31,-1), (53,1), (36,-1), (58,1), (29,-1), (34,-1), (56,1)], 3⟩,
    ⟨23, 56, 7, 17, [(56,1), (61,1), (27,-3), (32,-1), (54,1), (37,-1), (59,1), (64,3), (30,-1), (35,-1), (91,-3), (57,1), (62,1), (33,-1), (55,1), (38,-1), (60,1), (31,-1), (53,1), (36,-1), (58,1), (29,-1), (34,-1)], 3⟩]⟩

lemma phiCertifiedSegment110_checked : phiCertifiedSegment110.check=true := by decide +kernel

def phiCertifiedSegment111 : PhiCertifiedSegment :=
  ⟨(7/17), (12/29), 4, [
    ⟨7, 17, 12, 29, [(34,-1), (56,1), (27,-3), (61,1), (32,-1), (37,-1), (54,1), (59,1), (30,-1), (64,3), (35,-1), (57,1), (91,-3), (62,1), (33,-1), (38,-1), (55,1), (60,1), (31,-1), (36,-1), (53,1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment111_checked : phiCertifiedSegment111.check=true := by decide +kernel

def phiCertifiedSegment112 : PhiCertifiedSegment :=
  ⟨(12/29), (5/12), 5, [
    ⟨12, 29, 22, 53, [(29,-1), (58,1), (34,-1), (27,-3), (56,1), (32,-1), (61,1), (37,-1), (54,1), (30,-1), (59,1), (35,-1), (64,3), (57,1), (33,-1), (62,1), (91,-3), (38,-1), (55,1), (31,-1), (60,1), (36,-1), (53,1)], 5⟩,
    ⟨22, 53, 5, 12, [(53,1), (29,-1), (58,1), (34,-1), (27,-3), (56,1), (32,-1), (61,1), (37,-1), (54,1), (30,-1), (59,1), (35,-1), (64,3), (57,1), (33,-1), (62,1), (38,-1), (91,-3), (55,1), (31,-1), (60,1), (36,-1)], 5⟩]⟩

lemma phiCertifiedSegment112_checked : phiCertifiedSegment112.check=true := by decide +kernel

def phiCertifiedSegment113 : PhiCertifiedSegment :=
  ⟨(5/12), (8/19), 4, [
    ⟨5, 12, 38, 91, [(36,-1), (60,1), (29,-1), (53,1), (34,-1), (58,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (33,-1), (57,1), (38,-1), (62,1), (31,-1), (55,1), (91,-3)], 4⟩,
    ⟨38, 91, 23, 55, [(91,-3), (36,-1), (60,1), (29,-1), (53,1), (34,-1), (58,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (33,-1), (57,1), (38,-1), (62,1), (31,-1), (55,1)], 4⟩,
    ⟨23, 55, 13, 31, [(55,1), (36,-1), (91,-3), (60,1), (29,-1), (53,1), (34,-1), (58,1), (27,-3), (32,-1), (56,1), (37,-1), (61,1), (30,-1), (54,1), (35,-1), (59,1), (64,3), (33,-1), (57,1), (38,-1), (62,1), (31,-1)], 4⟩,
    ⟨13, 31, 8, 19, [(31,-1), (62,1), (55,1), (36,-1), (29,-1), (60,1), (91,-3), (53,1), (34,-1), (27,-3), (58,1), (32,-1), (56,1), (37,-1), (30,-1), (61,1), (54,1), (35,-1), (59,1), (33,-1), (64,3), (57,1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment113_checked : phiCertifiedSegment113.check=true := by decide +kernel

def phiCertifiedSegment114 : PhiCertifiedSegment :=
  ⟨(8/19), (11/26), 5, [
    ⟨8, 19, 27, 64, [(38,-1), (57,1), (31,-1), (62,1), (36,-1), (55,1), (29,-1), (60,1), (34,-1), (53,1), (91,-3), (27,-3), (58,1), (32,-1), (37,-1), (56,1), (30,-1), (61,1), (35,-1), (54,1), (59,1), (33,-1), (64,3)], 5⟩,
    ⟨27, 64, 11, 26, [(64,3), (38,-1), (57,1), (31,-1), (62,1), (36,-1), (55,1), (29,-1), (60,1), (34,-1), (53,1), (27,-3), (91,-3), (58,1), (32,-1), (37,-1), (56,1), (30,-1), (61,1), (35,-1), (54,1), (59,1), (33,-1)], 5⟩]⟩

lemma phiCertifiedSegment114_checked : phiCertifiedSegment114.check=true := by decide +kernel

def phiCertifiedSegment115 : PhiCertifiedSegment :=
  ⟨(11/26), (14/33), 4, [
    ⟨11, 26, 25, 59, [(38,-1), (64,3), (31,-1), (57,1), (36,-1), (62,1), (29,-1), (55,1), (34,-1), (60,1), (27,-3), (53,1), (91,-3), (32,-1), (58,1), (37,-1), (30,-1), (56,1), (35,-1), (61,1), (54,1), (33,-1), (59,1)], 4⟩,
    ⟨25, 59, 14, 33, [(59,1), (38,-1), (64,3), (31,-1), (57,1), (36,-1), (62,1), (29,-1), (55,1), (34,-1), (60,1), (27,-3), (53,1), (32,-1), (91,-3), (58,1), (37,-1), (30,-1), (56,1), (35,-1), (61,1), (54,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment115_checked : phiCertifiedSegment115.check=true := by decide +kernel

def phiCertifiedSegment116 : PhiCertifiedSegment :=
  ⟨(14/33), (3/7), 5, [
    ⟨14, 33, 23, 54, [(33,-1), (59,1), (38,-1), (31,-1), (64,3), (57,1), (36,-1), (29,-1), (62,1), (55,1), (34,-1), (27,-3), (60,1), (53,1), (32,-1), (58,1), (91,-3), (37,-1), (30,-1), (56,1), (35,-1), (61,1), (54,1)], 5⟩,
    ⟨23, 54, 26, 61, [(54,1), (33,-1), (59,1), (38,-1), (31,-1), (64,3), (57,1), (36,-1), (29,-1), (62,1), (55,1), (34,-1), (27,-3), (60,1), (53,1), (32,-1), (58,1), (37,-1), (91,-3), (30,-1), (56,1), (35,-1), (61,1)], 5⟩,
    ⟨26, 61, 3, 7, [(61,1), (54,1), (33,-1), (59,1), (38,-1), (31,-1), (64,3), (57,1), (36,-1), (29,-1), (62,1), (55,1), (34,-1), (27,-3), (60,1), (53,1), (32,-1), (58,1), (37,-1), (30,-1), (91,-3), (56,1), (35,-1)], 5⟩]⟩

lemma phiCertifiedSegment116_checked : phiCertifiedSegment116.check=true := by decide +kernel

def phiCertifiedSegment117 : PhiCertifiedSegment :=
  ⟨(3/7), (16/37), 7, [
    ⟨3, 7, 25, 58, [(35,-1), (56,1), (91,-3), (33,-1), (54,1), (61,1), (31,-1), (38,-1), (59,1), (29,-1), (36,-1), (57,1), (64,3), (27,-3), (34,-1), (55,1), (62,1), (32,-1), (53,1), (60,1), (30,-1), (37,-1), (58,1)], 7⟩,
    ⟨25, 58, 16, 37, [(58,1), (35,-1), (56,1), (33,-1), (91,-3), (54,1), (61,1), (31,-1), (38,-1), (59,1), (29,-1), (36,-1), (57,1), (64,3), (27,-3), (34,-1), (55,1), (62,1), (32,-1), (53,1), (60,1), (30,-1), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment117_checked : phiCertifiedSegment117.check=true := by decide +kernel

def phiCertifiedSegment118 : PhiCertifiedSegment :=
  ⟨(16/37), (13/30), 5, [
    ⟨16, 37, 13, 30, [(37,-1), (58,1), (35,-1), (56,1), (33,-1), (54,1), (91,-3), (61,1), (31,-1), (38,-1), (59,1), (29,-1), (36,-1), (57,1), (27,-3), (64,3), (34,-1), (55,1), (62,1), (32,-1), (53,1), (60,1), (30,-1)], 5⟩]⟩

lemma phiCertifiedSegment118_checked : phiCertifiedSegment118.check=true := by decide +kernel

def phiCertifiedSegment119 : PhiCertifiedSegment :=
  ⟨(13/30), (40/91), 4, [
    ⟨13, 30, 23, 53, [(30,-1), (60,1), (37,-1), (58,1), (35,-1), (56,1), (33,-1), (54,1), (31,-1), (61,1), (91,-3), (38,-1), (29,-1), (59,1), (36,-1), (27,-3), (57,1), (34,-1), (64,3), (55,1), (32,-1), (62,1), (53,1)], 4⟩,
    ⟨23, 53, 10, 23, [(53,1), (30,-1), (60,1), (37,-1), (58,1), (35,-1), (56,1), (33,-1), (54,1), (31,-1), (61,1), (38,-1), (91,-3), (29,-1), (59,1), (36,-1), (27,-3), (57,1), (34,-1), (64,3), (55,1), (32,-1), (62,1)], 4⟩,
    ⟨10, 23, 27, 62, [(30,-1), (53,1), (37,-1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (54,1), (38,-1), (61,1), (91,-3), (29,-1), (36,-1), (59,1), (27,-3), (34,-1), (57,1), (64,3), (32,-1), (55,1), (62,1)], 4⟩,
    ⟨27, 62, 24, 55, [(62,1), (30,-1), (53,1), (37,-1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (54,1), (38,-1), (61,1), (29,-1), (91,-3), (36,-1), (59,1), (27,-3), (34,-1), (57,1), (64,3), (32,-1), (55,1)], 4⟩,
    ⟨24, 55, 7, 16, [(55,1), (62,1), (30,-1), (53,1), (37,-1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (54,1), (38,-1), (61,1), (29,-1), (36,-1), (91,-3), (59,1), (27,-3), (34,-1), (57,1), (64,3), (32,-1)], 4⟩,
    ⟨7, 16, 25, 57, [(32,-1), (64,3), (55,1), (30,-1), (62,1), (37,-1), (53,1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (38,-1), (54,1), (29,-1), (61,1), (36,-1), (27,-3), (59,1), (91,-3), (34,-1), (57,1)], 4⟩,
    ⟨25, 57, 40, 91, [(57,1), (32,-1), (64,3), (55,1), (30,-1), (62,1), (37,-1), (53,1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (38,-1), (54,1), (29,-1), (61,1), (36,-1), (27,-3), (59,1), (34,-1), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment119_checked : phiCertifiedSegment119.check=true := by decide +kernel

def phiCertifiedSegment120 : PhiCertifiedSegment :=
  ⟨(40/91), (4/9), 7, [
    ⟨40, 91, 11, 25, [(91,-3), (57,1), (32,-1), (64,3), (55,1), (30,-1), (62,1), (37,-1), (53,1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (38,-1), (54,1), (29,-1), (61,1), (36,-1), (27,-3), (59,1), (34,-1)], 7⟩,
    ⟨11, 25, 26, 59, [(91,-3), (32,-1), (57,1), (64,3), (30,-1), (55,1), (37,-1), (62,1), (53,1), (35,-1), (60,1), (33,-1), (58,1), (31,-1), (56,1), (38,-1), (29,-1), (54,1), (36,-1), (61,1), (27,-3), (34,-1), (59,1)], 7⟩,
    ⟨26, 59, 15, 34, [(59,1), (32,-1), (91,-3), (57,1), (64,3), (30,-1), (55,1), (37,-1), (62,1), (53,1), (35,-1), (60,1), (33,-1), (58,1), (31,-1), (56,1), (38,-1), (29,-1), (54,1), (36,-1), (61,1), (27,-3), (34,-1)], 7⟩,
    ⟨15, 34, 27, 61, [(34,-1), (59,1), (32,-1), (57,1), (91,-3), (30,-1), (64,3), (55,1), (37,-1), (62,1), (53,1), (35,-1), (60,1), (33,-1), (58,1), (31,-1), (56,1), (38,-1), (29,-1), (54,1), (36,-1), (27,-3), (61,1)], 7⟩,
    ⟨27, 61, 4, 9, [(61,1), (34,-1), (59,1), (32,-1), (57,1), (30,-1), (91,-3), (64,3), (55,1), (37,-1), (62,1), (53,1), (35,-1), (60,1), (33,-1), (58,1), (31,-1), (56,1), (38,-1), (29,-1), (54,1), (36,-1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment120_checked : phiCertifiedSegment120.check=true := by decide +kernel

def phiCertifiedSegment121 : PhiCertifiedSegment :=
  ⟨(4/9), (5/11), 4, [
    ⟨4, 9, 25, 56, [(27,-3), (36,-1), (54,1), (34,-1), (61,1), (32,-1), (59,1), (30,-1), (57,1), (37,-1), (55,1), (64,3), (91,-3), (35,-1), (53,1), (62,1), (33,-1), (60,1), (31,-1), (58,1), (29,-1), (38,-1), (56,1)], 4⟩,
    ⟨25, 56, 17, 38, [(56,1), (27,-3), (36,-1), (54,1), (34,-1), (61,1), (32,-1), (59,1), (30,-1), (57,1), (37,-1), (55,1), (64,3), (35,-1), (91,-3), (53,1), (62,1), (33,-1), (60,1), (31,-1), (58,1), (29,-1), (38,-1)], 4⟩,
    ⟨17, 38, 13, 29, [(38,-1), (56,1), (27,-3), (36,-1), (54,1), (34,-1), (61,1), (32,-1), (59,1), (30,-1), (57,1), (37,-1), (55,1), (64,3), (35,-1), (53,1), (91,-3), (62,1), (33,-1), (60,1), (31,-1), (58,1), (29,-1)], 4⟩,
    ⟨13, 29, 9, 20, [(29,-1), (58,1), (38,-1), (27,-3), (56,1), (36,-1), (54,1), (34,-1), (32,-1), (61,1), (30,-1), (59,1), (57,1), (37,-1), (55,1), (35,-1), (64,3), (53,1), (33,-1), (62,1), (91,-3), (31,-1), (60,1)], 4⟩,
    ⟨9, 20, 41, 91, [(60,1), (29,-1), (38,-1), (58,1), (27,-3), (36,-1), (56,1), (34,-1), (54,1), (32,-1), (61,1), (30,-1), (59,1), (37,-1), (57,1), (35,-1), (55,1), (64,3), (33,-1), (53,1), (62,1), (31,-1), (91,-3)], 4⟩,
    ⟨41, 91, 14, 31, [(91,-3), (60,1), (29,-1), (38,-1), (58,1), (27,-3), (36,-1), (56,1), (34,-1), (54,1), (32,-1), (61,1), (30,-1), (59,1), (37,-1), (57,1), (35,-1), (55,1), (64,3), (33,-1), (53,1), (62,1), (31,-1)], 4⟩,
    ⟨14, 31, 24, 53, [(31,-1), (62,1), (29,-1), (60,1), (91,-3), (38,-1), (27,-3), (58,1), (36,-1), (56,1), (34,-1), (54,1), (32,-1), (30,-1), (61,1), (59,1), (37,-1), (57,1), (35,-1), (55,1), (33,-1), (64,3), (53,1)], 4⟩,
    ⟨24, 53, 29, 64, [(53,1), (31,-1), (62,1), (29,-1), (60,1), (38,-1), (91,-3), (27,-3), (58,1), (36,-1), (56,1), (34,-1), (54,1), (32,-1), (30,-1), (61,1), (59,1), (37,-1), (57,1), (35,-1), (55,1), (33,-1), (64,3)], 4⟩,
    ⟨29, 64, 5, 11, [(64,3), (53,1), (31,-1), (62,1), (29,-1), (60,1), (38,-1), (27,-3), (91,-3), (58,1), (36,-1), (56,1), (34,-1), (54,1), (32,-1), (30,-1), (61,1), (59,1), (37,-1), (57,1), (35,-1), (55,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment121_checked : phiCertifiedSegment121.check=true := by decide +kernel

def phiCertifiedSegment122 : PhiCertifiedSegment :=
  ⟨(5/11), (11/24), 5, [
    ⟨5, 11, 26, 57, [(33,-1), (55,1), (31,-1), (53,1), (64,3), (29,-1), (62,1), (27,-3), (38,-1), (60,1), (36,-1), (58,1), (91,-3), (34,-1), (56,1), (32,-1), (54,1), (30,-1), (61,1), (37,-1), (59,1), (35,-1), (57,1)], 5⟩,
    ⟨26, 57, 16, 35, [(57,1), (33,-1), (55,1), (31,-1), (53,1), (64,3), (29,-1), (62,1), (27,-3), (38,-1), (60,1), (36,-1), (58,1), (34,-1), (91,-3), (56,1), (32,-1), (54,1), (30,-1), (61,1), (37,-1), (59,1), (35,-1)], 5⟩,
    ⟨16, 35, 27, 59, [(35,-1), (57,1), (33,-1), (55,1), (31,-1), (53,1), (29,-1), (64,3), (27,-3), (62,1), (38,-1), (60,1), (36,-1), (58,1), (34,-1), (56,1), (91,-3), (32,-1), (54,1), (30,-1), (61,1), (37,-1), (59,1)], 5⟩,
    ⟨27, 59, 11, 24, [(59,1), (35,-1), (57,1), (33,-1), (55,1), (31,-1), (53,1), (29,-1), (64,3), (27,-3), (62,1), (38,-1), (60,1), (36,-1), (58,1), (34,-1), (56,1), (32,-1), (91,-3), (54,1), (30,-1), (61,1), (37,-1)], 5⟩]⟩

lemma phiCertifiedSegment122_checked : phiCertifiedSegment122.check=true := by decide +kernel

def phiCertifiedSegment123 : PhiCertifiedSegment :=
  ⟨(11/24), (17/37), 4, [
    ⟨11, 24, 28, 61, [(35,-1), (59,1), (33,-1), (57,1), (31,-1), (55,1), (29,-1), (53,1), (64,3), (27,-3), (38,-1), (62,1), (36,-1), (60,1), (34,-1), (58,1), (32,-1), (56,1), (91,-3), (30,-1), (54,1), (37,-1), (61,1)], 4⟩,
    ⟨28, 61, 17, 37, [(61,1), (35,-1), (59,1), (33,-1), (57,1), (31,-1), (55,1), (29,-1), (53,1), (64,3), (27,-3), (38,-1), (62,1), (36,-1), (60,1), (34,-1), (58,1), (32,-1), (56,1), (30,-1), (91,-3), (54,1), (37,-1)], 4⟩]⟩

lemma phiCertifiedSegment123_checked : phiCertifiedSegment123.check=true := by decide +kernel

def phiCertifiedSegment124 : PhiCertifiedSegment :=
  ⟨(17/37), (6/13), 5, [
    ⟨17, 37, 6, 13, [(37,-1), (61,1), (35,-1), (59,1), (33,-1), (57,1), (31,-1), (55,1), (29,-1), (53,1), (27,-3), (64,3), (38,-1), (62,1), (36,-1), (60,1), (34,-1), (58,1), (32,-1), (56,1), (30,-1), (54,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment124_checked : phiCertifiedSegment124.check=true := by decide +kernel

def phiCertifiedSegment125 : PhiCertifiedSegment :=
  ⟨(6/13), (13/28), 4, [
    ⟨6, 13, 25, 54, [(91,-3), (37,-1), (35,-1), (61,1), (33,-1), (59,1), (31,-1), (57,1), (29,-1), (55,1), (27,-3), (53,1), (38,-1), (64,3), (36,-1), (62,1), (34,-1), (60,1), (32,-1), (58,1), (30,-1), (56,1), (54,1)], 4⟩,
    ⟨25, 54, 13, 28, [(54,1), (37,-1), (91,-3), (35,-1), (61,1), (33,-1), (59,1), (31,-1), (57,1), (29,-1), (55,1), (27,-3), (53,1), (38,-1), (64,3), (36,-1), (62,1), (34,-1), (60,1), (32,-1), (58,1), (30,-1), (56,1)], 4⟩]⟩

lemma phiCertifiedSegment125_checked : phiCertifiedSegment125.check=true := by decide +kernel

def phiCertifiedSegment126 : PhiCertifiedSegment :=
  ⟨(13/28), (8/17), 3, [
    ⟨13, 28, 27, 58, [(56,1), (54,1), (37,-1), (35,-1), (91,-3), (33,-1), (61,1), (31,-1), (59,1), (29,-1), (57,1), (27,-3), (55,1), (53,1), (38,-1), (36,-1), (64,3), (34,-1), (62,1), (32,-1), (60,1), (30,-1), (58,1)], 3⟩,
    ⟨27, 58, 7, 15, [(58,1), (56,1), (54,1), (37,-1), (35,-1), (33,-1), (91,-3), (61,1), (31,-1), (59,1), (29,-1), (57,1), (27,-3), (55,1), (53,1), (38,-1), (36,-1), (64,3), (34,-1), (62,1), (32,-1), (60,1), (30,-1)], 3⟩,
    ⟨7, 15, 29, 62, [(30,-1), (60,1), (58,1), (56,1), (54,1), (37,-1), (35,-1), (33,-1), (31,-1), (61,1), (91,-3), (29,-1), (59,1), (27,-3), (57,1), (55,1), (38,-1), (53,1), (36,-1), (34,-1), (64,3), (32,-1), (62,1)], 3⟩,
    ⟨29, 62, 15, 32, [(62,1), (30,-1), (60,1), (58,1), (56,1), (54,1), (37,-1), (35,-1), (33,-1), (31,-1), (61,1), (29,-1), (91,-3), (59,1), (27,-3), (57,1), (55,1), (38,-1), (53,1), (36,-1), (34,-1), (64,3), (32,-1)], 3⟩,
    ⟨15, 32, 8, 17, [(32,-1), (64,3), (30,-1), (62,1), (60,1), (58,1), (56,1), (54,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (61,1), (27,-3), (59,1), (91,-3), (57,1), (55,1), (38,-1), (53,1), (36,-1), (34,-1)], 3⟩]⟩

lemma phiCertifiedSegment126_checked : phiCertifiedSegment126.check=true := by decide +kernel

def phiCertifiedSegment127 : PhiCertifiedSegment :=
  ⟨(8/17), (17/36), 4, [
    ⟨8, 17, 25, 53, [(34,-1), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (56,1), (37,-1), (54,1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1), (57,1), (91,-3), (38,-1), (55,1), (36,-1), (53,1)], 4⟩,
    ⟨25, 53, 17, 36, [(53,1), (34,-1), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (56,1), (37,-1), (54,1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1), (57,1), (38,-1), (91,-3), (55,1), (36,-1)], 4⟩]⟩

lemma phiCertifiedSegment127_checked : phiCertifiedSegment127.check=true := by decide +kernel

def phiCertifiedSegment128 : PhiCertifiedSegment :=
  ⟨(17/36), (9/19), 5, [
    ⟨17, 36, 43, 91, [(36,-1), (53,1), (34,-1), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (56,1), (37,-1), (54,1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1), (57,1), (38,-1), (55,1), (91,-3)], 5⟩,
    ⟨43, 91, 26, 55, [(91,-3), (36,-1), (53,1), (34,-1), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (56,1), (37,-1), (54,1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1), (57,1), (38,-1), (55,1)], 5⟩,
    ⟨26, 55, 9, 19, [(55,1), (36,-1), (91,-3), (53,1), (34,-1), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (56,1), (37,-1), (54,1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1), (57,1), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment128_checked : phiCertifiedSegment128.check=true := by decide +kernel

def phiCertifiedSegment129 : PhiCertifiedSegment :=
  ⟨(9/19), (10/21), 6, [
    ⟨9, 19, 28, 59, [(38,-1), (57,1), (36,-1), (55,1), (34,-1), (53,1), (91,-3), (32,-1), (30,-1), (64,3), (62,1), (60,1), (58,1), (37,-1), (56,1), (35,-1), (54,1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1), (59,1)], 6⟩,
    ⟨28, 59, 29, 61, [(59,1), (38,-1), (57,1), (36,-1), (55,1), (34,-1), (53,1), (32,-1), (91,-3), (30,-1), (64,3), (62,1), (60,1), (58,1), (37,-1), (56,1), (35,-1), (54,1), (33,-1), (31,-1), (29,-1), (27,-3), (61,1)], 6⟩,
    ⟨29, 61, 10, 21, [(61,1), (59,1), (38,-1), (57,1), (36,-1), (55,1), (34,-1), (53,1), (32,-1), (30,-1), (91,-3), (64,3), (62,1), (60,1), (58,1), (37,-1), (56,1), (35,-1), (54,1), (33,-1), (31,-1), (29,-1), (27,-3)], 6⟩]⟩

lemma phiCertifiedSegment129_checked : phiCertifiedSegment129.check=true := by decide +kernel

def phiCertifiedSegment130 : PhiCertifiedSegment :=
  ⟨(10/21), (11/23), 7, [
    ⟨10, 21, 11, 23, [(61,1), (38,-1), (59,1), (36,-1), (57,1), (34,-1), (55,1), (32,-1), (53,1), (30,-1), (91,-3), (64,3), (62,1), (60,1), (37,-1), (58,1), (35,-1), (56,1), (33,-1), (54,1), (31,-1), (29,-1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment130_checked : phiCertifiedSegment130.check=true := by decide +kernel

def phiCertifiedSegment131 : PhiCertifiedSegment :=
  ⟨(11/23), (12/25), 8, [
    ⟨11, 23, 12, 25, [(38,-1), (61,1), (36,-1), (59,1), (34,-1), (57,1), (32,-1), (55,1), (30,-1), (53,1), (91,-3), (64,3), (62,1), (37,-1), (60,1), (35,-1), (58,1), (33,-1), (56,1), (31,-1), (54,1), (29,-1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment131_checked : phiCertifiedSegment131.check=true := by decide +kernel

def phiCertifiedSegment132 : PhiCertifiedSegment :=
  ⟨(12/25), (13/27), 9, [
    ⟨12, 25, 13, 27, [(38,-1), (36,-1), (61,1), (34,-1), (59,1), (32,-1), (57,1), (30,-1), (55,1), (53,1), (91,-3), (64,3), (37,-1), (62,1), (35,-1), (60,1), (33,-1), (58,1), (31,-1), (56,1), (29,-1), (54,1), (27,-3)], 9⟩]⟩

lemma phiCertifiedSegment132_checked : phiCertifiedSegment132.check=true := by decide +kernel

def phiCertifiedSegment133 : PhiCertifiedSegment :=
  ⟨(13/27), (16/33), 4, [
    ⟨13, 27, 27, 56, [(27,-3), (54,1), (38,-1), (36,-1), (34,-1), (61,1), (32,-1), (59,1), (30,-1), (57,1), (55,1), (53,1), (37,-1), (64,3), (91,-3), (35,-1), (62,1), (33,-1), (60,1), (31,-1), (58,1), (29,-1), (56,1)], 4⟩,
    ⟨27, 56, 14, 29, [(56,1), (27,-3), (54,1), (38,-1), (36,-1), (34,-1), (61,1), (32,-1), (59,1), (30,-1), (57,1), (55,1), (53,1), (37,-1), (64,3), (35,-1), (91,-3), (62,1), (33,-1), (60,1), (31,-1), (58,1), (29,-1)], 4⟩,
    ⟨14, 29, 29, 60, [(29,-1), (58,1), (27,-3), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (61,1), (30,-1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (64,3), (33,-1), (62,1), (91,-3), (31,-1), (60,1)], 4⟩,
    ⟨29, 60, 44, 91, [(60,1), (29,-1), (58,1), (27,-3), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (61,1), (30,-1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (64,3), (33,-1), (62,1), (31,-1), (91,-3)], 4⟩,
    ⟨44, 91, 15, 31, [(91,-3), (60,1), (29,-1), (58,1), (27,-3), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (61,1), (30,-1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (64,3), (33,-1), (62,1), (31,-1)], 4⟩,
    ⟨15, 31, 31, 64, [(31,-1), (62,1), (29,-1), (60,1), (91,-3), (27,-3), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1), (64,3)], 4⟩,
    ⟨31, 64, 16, 33, [(64,3), (31,-1), (62,1), (29,-1), (60,1), (27,-3), (91,-3), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment133_checked : phiCertifiedSegment133.check=true := by decide +kernel

def phiCertifiedSegment134 : PhiCertifiedSegment :=
  ⟨(16/33), (1/2), 5, [
    ⟨16, 33, 17, 35, [(33,-1), (31,-1), (64,3), (29,-1), (62,1), (27,-3), (60,1), (58,1), (91,-3), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1)], 5⟩,
    ⟨17, 35, 18, 37, [(35,-1), (33,-1), (31,-1), (29,-1), (64,3), (27,-3), (62,1), (60,1), (58,1), (56,1), (91,-3), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1), (53,1), (37,-1)], 5⟩,
    ⟨18, 37, 26, 53, [(37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (91,-3), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1), (53,1)], 5⟩,
    ⟨26, 53, 27, 55, [(53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (91,-3), (36,-1), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1), (55,1)], 5⟩,
    ⟨27, 55, 28, 57, [(55,1), (53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (36,-1), (91,-3), (34,-1), (32,-1), (30,-1), (61,1), (59,1), (57,1)], 5⟩,
    ⟨28, 57, 29, 59, [(57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (91,-3), (32,-1), (30,-1), (61,1), (59,1)], 5⟩,
    ⟨29, 59, 30, 61, [(59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (91,-3), (30,-1), (61,1)], 5⟩,
    ⟨30, 61, 45, 91, [(61,1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1), (91,-3)], 5⟩,
    ⟨45, 91, 1, 2, [(91,-3), (61,1), (59,1), (57,1), (55,1), (53,1), (37,-1), (35,-1), (33,-1), (31,-1), (29,-1), (27,-3), (64,3), (62,1), (60,1), (58,1), (56,1), (54,1), (38,-1), (36,-1), (34,-1), (32,-1), (30,-1)], 5⟩]⟩

lemma phiCertifiedSegment134_checked : phiCertifiedSegment134.check=true := by decide +kernel

def phiCertifiedSegment135 : PhiCertifiedSegment :=
  ⟨(1/2), (19/37), 3, [
    ⟨1, 2, 46, 91, [(30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (61,1), (91,-3)], 3⟩,
    ⟨46, 91, 31, 61, [(91,-3), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (61,1)], 3⟩,
    ⟨31, 61, 30, 59, [(61,1), (30,-1), (91,-3), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1)], 3⟩,
    ⟨30, 59, 29, 57, [(59,1), (61,1), (30,-1), (32,-1), (91,-3), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1)], 3⟩,
    ⟨29, 57, 28, 55, [(57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (91,-3), (36,-1), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1), (55,1)], 3⟩,
    ⟨28, 55, 27, 53, [(55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (91,-3), (38,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (53,1)], 3⟩,
    ⟨27, 53, 19, 37, [(53,1), (55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (91,-3), (54,1), (56,1), (58,1), (60,1), (62,1), (64,3), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1)], 3⟩]⟩

lemma phiCertifiedSegment135_checked : phiCertifiedSegment135.check=true := by decide +kernel

def phiCertifiedSegment136 : PhiCertifiedSegment :=
  ⟨(19/37), (16/31), 4, [
    ⟨19, 37, 18, 35, [(37,-1), (53,1), (55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (91,-3), (56,1), (58,1), (60,1), (62,1), (27,-3), (64,3), (29,-1), (31,-1), (33,-1), (35,-1)], 4⟩,
    ⟨18, 35, 17, 33, [(35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (91,-3), (58,1), (60,1), (27,-3), (62,1), (29,-1), (64,3), (31,-1), (33,-1)], 4⟩,
    ⟨17, 33, 33, 64, [(33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (91,-3), (27,-3), (60,1), (29,-1), (62,1), (31,-1), (64,3)], 4⟩,
    ⟨33, 64, 16, 31, [(64,3), (33,-1), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (61,1), (30,-1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (58,1), (27,-3), (91,-3), (60,1), (29,-1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment136_checked : phiCertifiedSegment136.check=true := by decide +kernel

def phiCertifiedSegment137 : PhiCertifiedSegment :=
  ⟨(16/31), (47/91), 5, [
    ⟨16, 31, 47, 91, [(31,-1), (62,1), (33,-1), (64,3), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (30,-1), (61,1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (27,-3), (58,1), (29,-1), (60,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment137_checked : phiCertifiedSegment137.check=true := by decide +kernel

def phiCertifiedSegment138 : PhiCertifiedSegment :=
  ⟨(47/91), (14/27), 7, [
    ⟨47, 91, 31, 60, [(91,-3), (31,-1), (62,1), (33,-1), (64,3), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (30,-1), (61,1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (27,-3), (58,1), (29,-1), (60,1)], 7⟩,
    ⟨31, 60, 15, 29, [(60,1), (31,-1), (91,-3), (62,1), (33,-1), (64,3), (35,-1), (37,-1), (53,1), (55,1), (57,1), (59,1), (30,-1), (61,1), (32,-1), (34,-1), (36,-1), (38,-1), (54,1), (56,1), (27,-3), (58,1), (29,-1)], 7⟩,
    ⟨15, 29, 29, 56, [(29,-1), (58,1), (31,-1), (60,1), (33,-1), (62,1), (91,-3), (35,-1), (64,3), (37,-1), (53,1), (55,1), (57,1), (30,-1), (59,1), (32,-1), (61,1), (34,-1), (36,-1), (38,-1), (54,1), (27,-3), (56,1)], 7⟩,
    ⟨29, 56, 14, 27, [(56,1), (29,-1), (58,1), (31,-1), (60,1), (33,-1), (62,1), (35,-1), (91,-3), (64,3), (37,-1), (53,1), (55,1), (57,1), (30,-1), (59,1), (32,-1), (61,1), (34,-1), (36,-1), (38,-1), (54,1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment138_checked : phiCertifiedSegment138.check=true := by decide +kernel

def phiCertifiedSegment139 : PhiCertifiedSegment :=
  ⟨(14/27), (8/15), 4, [
    ⟨14, 27, 13, 25, [(27,-3), (54,1), (29,-1), (56,1), (31,-1), (58,1), (33,-1), (60,1), (35,-1), (62,1), (37,-1), (64,3), (91,-3), (53,1), (55,1), (30,-1), (57,1), (32,-1), (59,1), (34,-1), (61,1), (36,-1), (38,-1)], 4⟩,
    ⟨13, 25, 12, 23, [(27,-3), (29,-1), (54,1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (37,-1), (62,1), (64,3), (91,-3), (53,1), (30,-1), (55,1), (32,-1), (57,1), (34,-1), (59,1), (36,-1), (61,1), (38,-1)], 4⟩,
    ⟨12, 23, 11, 21, [(27,-3), (29,-1), (31,-1), (54,1), (33,-1), (56,1), (35,-1), (58,1), (37,-1), (60,1), (62,1), (64,3), (91,-3), (30,-1), (53,1), (32,-1), (55,1), (34,-1), (57,1), (36,-1), (59,1), (38,-1), (61,1)], 4⟩,
    ⟨11, 21, 32, 61, [(27,-3), (29,-1), (31,-1), (33,-1), (54,1), (35,-1), (56,1), (37,-1), (58,1), (60,1), (62,1), (64,3), (91,-3), (30,-1), (32,-1), (53,1), (34,-1), (55,1), (36,-1), (57,1), (38,-1), (59,1), (61,1)], 4⟩,
    ⟨32, 61, 31, 59, [(61,1), (27,-3), (29,-1), (31,-1), (33,-1), (54,1), (35,-1), (56,1), (37,-1), (58,1), (60,1), (62,1), (64,3), (30,-1), (91,-3), (32,-1), (53,1), (34,-1), (55,1), (36,-1), (57,1), (38,-1), (59,1)], 4⟩,
    ⟨31, 59, 10, 19, [(59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (54,1), (35,-1), (56,1), (37,-1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (91,-3), (53,1), (34,-1), (55,1), (36,-1), (57,1), (38,-1)], 4⟩,
    ⟨10, 19, 29, 55, [(38,-1), (57,1), (59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (54,1), (37,-1), (56,1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (34,-1), (53,1), (91,-3), (36,-1), (55,1)], 4⟩,
    ⟨29, 55, 48, 91, [(55,1), (38,-1), (57,1), (59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (54,1), (37,-1), (56,1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (34,-1), (53,1), (36,-1), (91,-3)], 4⟩,
    ⟨48, 91, 19, 36, [(91,-3), (55,1), (38,-1), (57,1), (59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (54,1), (37,-1), (56,1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (34,-1), (53,1), (36,-1)], 4⟩,
    ⟨19, 36, 28, 53, [(36,-1), (55,1), (91,-3), (38,-1), (57,1), (59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (54,1), (37,-1), (56,1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (34,-1), (53,1)], 4⟩,
    ⟨28, 53, 9, 17, [(53,1), (36,-1), (55,1), (38,-1), (91,-3), (57,1), (59,1), (61,1), (27,-3), (29,-1), (31,-1), (33,-1), (35,-1), (54,1), (37,-1), (56,1), (58,1), (60,1), (62,1), (64,3), (30,-1), (32,-1), (34,-1)], 4⟩,
    ⟨9, 17, 17, 32, [(34,-1), (36,-1), (53,1), (38,-1), (55,1), (57,1), (91,-3), (59,1), (27,-3), (61,1), (29,-1), (31,-1), (33,-1), (35,-1), (37,-1), (54,1), (56,1), (58,1), (60,1), (62,1), (30,-1), (64,3), (32,-1)], 4⟩,
    ⟨17, 32, 33, 62, [(32,-1), (64,3), (34,-1), (36,-1), (53,1), (38,-1), (55,1), (57,1), (27,-3), (59,1), (91,-3), (29,-1), (61,1), (31,-1), (33,-1), (35,-1), (37,-1), (54,1), (56,1), (58,1), (60,1), (30,-1), (62,1)], 4⟩,
    ⟨33, 62, 8, 15, [(62,1), (32,-1), (64,3), (34,-1), (36,-1), (53,1), (38,-1), (55,1), (57,1), (27,-3), (59,1), (29,-1), (91,-3), (61,1), (31,-1), (33,-1), (35,-1), (37,-1), (54,1), (56,1), (58,1), (60,1), (30,-1)], 4⟩]⟩

lemma phiCertifiedSegment139_checked : phiCertifiedSegment139.check=true := by decide +kernel

def phiCertifiedSegment140 : PhiCertifiedSegment :=
  ⟨(8/15), (7/13), 5, [
    ⟨8, 15, 31, 58, [(30,-1), (60,1), (32,-1), (62,1), (34,-1), (64,3), (36,-1), (38,-1), (53,1), (55,1), (27,-3), (57,1), (29,-1), (59,1), (31,-1), (61,1), (91,-3), (33,-1), (35,-1), (37,-1), (54,1), (56,1), (58,1)], 5⟩,
    ⟨31, 58, 15, 28, [(58,1), (30,-1), (60,1), (32,-1), (62,1), (34,-1), (64,3), (36,-1), (38,-1), (53,1), (55,1), (27,-3), (57,1), (29,-1), (59,1), (31,-1), (61,1), (33,-1), (91,-3), (35,-1), (37,-1), (54,1), (56,1)], 5⟩,
    ⟨15, 28, 29, 54, [(56,1), (30,-1), (58,1), (32,-1), (60,1), (34,-1), (62,1), (36,-1), (64,3), (38,-1), (53,1), (27,-3), (55,1), (29,-1), (57,1), (31,-1), (59,1), (33,-1), (61,1), (35,-1), (91,-3), (37,-1), (54,1)], 5⟩,
    ⟨29, 54, 7, 13, [(54,1), (56,1), (30,-1), (58,1), (32,-1), (60,1), (34,-1), (62,1), (36,-1), (64,3), (38,-1), (53,1), (27,-3), (55,1), (29,-1), (57,1), (31,-1), (59,1), (33,-1), (61,1), (35,-1), (37,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment140_checked : phiCertifiedSegment140.check=true := by decide +kernel

def phiCertifiedSegment141 : PhiCertifiedSegment :=
  ⟨(7/13), (20/37), 8, [
    ⟨7, 13, 20, 37, [(91,-3), (54,1), (30,-1), (56,1), (32,-1), (58,1), (34,-1), (60,1), (36,-1), (62,1), (38,-1), (64,3), (27,-3), (53,1), (29,-1), (55,1), (31,-1), (57,1), (33,-1), (59,1), (35,-1), (61,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment141_checked : phiCertifiedSegment141.check=true := by decide +kernel

def phiCertifiedSegment142 : PhiCertifiedSegment :=
  ⟨(20/37), (19/35), 5, [
    ⟨20, 37, 33, 61, [(37,-1), (54,1), (91,-3), (30,-1), (56,1), (32,-1), (58,1), (34,-1), (60,1), (36,-1), (62,1), (38,-1), (27,-3), (64,3), (53,1), (29,-1), (55,1), (31,-1), (57,1), (33,-1), (59,1), (35,-1), (61,1)], 5⟩,
    ⟨33, 61, 13, 24, [(61,1), (37,-1), (54,1), (30,-1), (91,-3), (56,1), (32,-1), (58,1), (34,-1), (60,1), (36,-1), (62,1), (38,-1), (27,-3), (64,3), (53,1), (29,-1), (55,1), (31,-1), (57,1), (33,-1), (59,1), (35,-1)], 5⟩,
    ⟨13, 24, 32, 59, [(37,-1), (61,1), (30,-1), (54,1), (91,-3), (32,-1), (56,1), (34,-1), (58,1), (36,-1), (60,1), (38,-1), (62,1), (27,-3), (64,3), (29,-1), (53,1), (31,-1), (55,1), (33,-1), (57,1), (35,-1), (59,1)], 5⟩,
    ⟨32, 59, 19, 35, [(59,1), (37,-1), (61,1), (30,-1), (54,1), (32,-1), (91,-3), (56,1), (34,-1), (58,1), (36,-1), (60,1), (38,-1), (62,1), (27,-3), (64,3), (29,-1), (53,1), (31,-1), (55,1), (33,-1), (57,1), (35,-1)], 5⟩]⟩

lemma phiCertifiedSegment142_checked : phiCertifiedSegment142.check=true := by decide +kernel

def phiCertifiedSegment143 : PhiCertifiedSegment :=
  ⟨(19/35), (17/31), 4, [
    ⟨19, 35, 31, 57, [(35,-1), (59,1), (37,-1), (61,1), (30,-1), (54,1), (32,-1), (56,1), (91,-3), (34,-1), (58,1), (36,-1), (60,1), (38,-1), (27,-3), (62,1), (29,-1), (64,3), (53,1), (31,-1), (55,1), (33,-1), (57,1)], 4⟩,
    ⟨31, 57, 6, 11, [(57,1), (35,-1), (59,1), (37,-1), (61,1), (30,-1), (54,1), (32,-1), (56,1), (34,-1), (91,-3), (58,1), (36,-1), (60,1), (38,-1), (27,-3), (62,1), (29,-1), (64,3), (53,1), (31,-1), (55,1), (33,-1)], 4⟩,
    ⟨6, 11, 35, 64, [(33,-1), (55,1), (35,-1), (57,1), (37,-1), (59,1), (61,1), (30,-1), (32,-1), (54,1), (34,-1), (56,1), (36,-1), (58,1), (91,-3), (27,-3), (38,-1), (60,1), (29,-1), (62,1), (31,-1), (53,1), (64,3)], 4⟩,
    ⟨35, 64, 29, 53, [(64,3), (33,-1), (55,1), (35,-1), (57,1), (37,-1), (59,1), (61,1), (30,-1), (32,-1), (54,1), (34,-1), (56,1), (36,-1), (58,1), (27,-3), (91,-3), (38,-1), (60,1), (29,-1), (62,1), (31,-1), (53,1)], 4⟩,
    ⟨29, 53, 17, 31, [(53,1), (64,3), (33,-1), (55,1), (35,-1), (57,1), (37,-1), (59,1), (61,1), (30,-1), (32,-1), (54,1), (34,-1), (56,1), (36,-1), (58,1), (27,-3), (38,-1), (91,-3), (60,1), (29,-1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment143_checked : phiCertifiedSegment143.check=true := by decide +kernel

def phiCertifiedSegment144 : PhiCertifiedSegment :=
  ⟨(17/31), (50/91), 5, [
    ⟨17, 31, 50, 91, [(31,-1), (62,1), (53,1), (33,-1), (64,3), (55,1), (35,-1), (57,1), (37,-1), (59,1), (30,-1), (61,1), (32,-1), (54,1), (34,-1), (56,1), (36,-1), (27,-3), (58,1), (38,-1), (29,-1), (60,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment144_checked : phiCertifiedSegment144.check=true := by decide +kernel

def phiCertifiedSegment145 : PhiCertifiedSegment :=
  ⟨(50/91), (16/29), 7, [
    ⟨50, 91, 11, 20, [(91,-3), (31,-1), (62,1), (53,1), (33,-1), (64,3), (55,1), (35,-1), (57,1), (37,-1), (59,1), (30,-1), (61,1), (32,-1), (54,1), (34,-1), (56,1), (36,-1), (27,-3), (58,1), (38,-1), (29,-1), (60,1)], 7⟩,
    ⟨11, 20, 16, 29, [(60,1), (31,-1), (91,-3), (62,1), (33,-1), (53,1), (64,3), (35,-1), (55,1), (37,-1), (57,1), (59,1), (30,-1), (61,1), (32,-1), (34,-1), (54,1), (36,-1), (56,1), (27,-3), (38,-1), (58,1), (29,-1)], 7⟩]⟩

lemma phiCertifiedSegment145_checked : phiCertifiedSegment145.check=true := by decide +kernel

def phiCertifiedSegment146 : PhiCertifiedSegment :=
  ⟨(16/29), (5/9), 8, [
    ⟨16, 29, 21, 38, [(29,-1), (58,1), (31,-1), (60,1), (33,-1), (62,1), (91,-3), (53,1), (35,-1), (64,3), (55,1), (37,-1), (57,1), (30,-1), (59,1), (32,-1), (61,1), (34,-1), (54,1), (36,-1), (27,-3), (56,1), (38,-1)], 8⟩,
    ⟨21, 38, 31, 56, [(38,-1), (29,-1), (58,1), (31,-1), (60,1), (33,-1), (62,1), (53,1), (91,-3), (35,-1), (64,3), (55,1), (37,-1), (57,1), (30,-1), (59,1), (32,-1), (61,1), (34,-1), (54,1), (36,-1), (27,-3), (56,1)], 8⟩,
    ⟨31, 56, 5, 9, [(56,1), (38,-1), (29,-1), (58,1), (31,-1), (60,1), (33,-1), (62,1), (53,1), (35,-1), (91,-3), (64,3), (55,1), (37,-1), (57,1), (30,-1), (59,1), (32,-1), (61,1), (34,-1), (54,1), (36,-1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment146_checked : phiCertifiedSegment146.check=true := by decide +kernel

def phiCertifiedSegment147 : PhiCertifiedSegment :=
  ⟨(5/9), (19/33), 4, [
    ⟨5, 9, 34, 61, [(27,-3), (36,-1), (54,1), (29,-1), (38,-1), (56,1), (31,-1), (58,1), (33,-1), (60,1), (35,-1), (53,1), (62,1), (37,-1), (55,1), (64,3), (91,-3), (30,-1), (57,1), (32,-1), (59,1), (34,-1), (61,1)], 4⟩,
    ⟨34, 61, 19, 34, [(61,1), (27,-3), (36,-1), (54,1), (29,-1), (38,-1), (56,1), (31,-1), (58,1), (33,-1), (60,1), (35,-1), (53,1), (62,1), (37,-1), (55,1), (64,3), (30,-1), (91,-3), (57,1), (32,-1), (59,1), (34,-1)], 4⟩,
    ⟨19, 34, 33, 59, [(34,-1), (27,-3), (61,1), (36,-1), (54,1), (29,-1), (38,-1), (56,1), (31,-1), (58,1), (33,-1), (60,1), (35,-1), (53,1), (62,1), (37,-1), (55,1), (30,-1), (64,3), (57,1), (91,-3), (32,-1), (59,1)], 4⟩,
    ⟨33, 59, 14, 25, [(59,1), (34,-1), (27,-3), (61,1), (36,-1), (54,1), (29,-1), (38,-1), (56,1), (31,-1), (58,1), (33,-1), (60,1), (35,-1), (53,1), (62,1), (37,-1), (55,1), (30,-1), (64,3), (57,1), (32,-1), (91,-3)], 4⟩,
    ⟨14, 25, 51, 91, [(34,-1), (59,1), (27,-3), (36,-1), (61,1), (29,-1), (54,1), (38,-1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (53,1), (37,-1), (62,1), (30,-1), (55,1), (64,3), (32,-1), (57,1), (91,-3)], 4⟩,
    ⟨51, 91, 32, 57, [(91,-3), (34,-1), (59,1), (27,-3), (36,-1), (61,1), (29,-1), (54,1), (38,-1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (53,1), (37,-1), (62,1), (30,-1), (55,1), (64,3), (32,-1), (57,1)], 4⟩,
    ⟨32, 57, 9, 16, [(57,1), (34,-1), (91,-3), (59,1), (27,-3), (36,-1), (61,1), (29,-1), (54,1), (38,-1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (53,1), (37,-1), (62,1), (30,-1), (55,1), (64,3), (32,-1)], 4⟩,
    ⟨9, 16, 31, 55, [(32,-1), (64,3), (57,1), (34,-1), (27,-3), (59,1), (91,-3), (36,-1), (29,-1), (61,1), (38,-1), (54,1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (37,-1), (53,1), (30,-1), (62,1), (55,1)], 4⟩,
    ⟨31, 55, 35, 62, [(55,1), (32,-1), (64,3), (57,1), (34,-1), (27,-3), (59,1), (36,-1), (91,-3), (29,-1), (61,1), (38,-1), (54,1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (37,-1), (53,1), (30,-1), (62,1)], 4⟩,
    ⟨35, 62, 13, 23, [(62,1), (55,1), (32,-1), (64,3), (57,1), (34,-1), (27,-3), (59,1), (36,-1), (29,-1), (91,-3), (61,1), (38,-1), (54,1), (31,-1), (56,1), (33,-1), (58,1), (35,-1), (60,1), (37,-1), (53,1), (30,-1)], 4⟩,
    ⟨13, 23, 30, 53, [(62,1), (32,-1), (55,1), (64,3), (34,-1), (57,1), (27,-3), (36,-1), (59,1), (29,-1), (91,-3), (38,-1), (61,1), (31,-1), (54,1), (33,-1), (56,1), (35,-1), (58,1), (37,-1), (60,1), (30,-1), (53,1)], 4⟩,
    ⟨30, 53, 17, 30, [(53,1), (62,1), (32,-1), (55,1), (64,3), (34,-1), (57,1), (27,-3), (36,-1), (59,1), (29,-1), (38,-1), (91,-3), (61,1), (31,-1), (54,1), (33,-1), (56,1), (35,-1), (58,1), (37,-1), (60,1), (30,-1)], 4⟩,
    ⟨17, 30, 21, 37, [(30,-1), (60,1), (53,1), (32,-1), (62,1), (55,1), (34,-1), (64,3), (27,-3), (57,1), (36,-1), (29,-1), (59,1), (38,-1), (31,-1), (61,1), (91,-3), (54,1), (33,-1), (56,1), (35,-1), (58,1), (37,-1)], 4⟩,
    ⟨21, 37, 33, 58, [(37,-1), (30,-1), (60,1), (53,1), (32,-1), (62,1), (55,1), (34,-1), (27,-3), (64,3), (57,1), (36,-1), (29,-1), (59,1), (38,-1), (31,-1), (61,1), (54,1), (91,-3), (33,-1), (56,1), (35,-1), (58,1)], 4⟩,
    ⟨33, 58, 4, 7, [(58,1), (37,-1), (30,-1), (60,1), (53,1), (32,-1), (62,1), (55,1), (34,-1), (27,-3), (64,3), (57,1), (36,-1), (29,-1), (59,1), (38,-1), (31,-1), (61,1), (54,1), (33,-1), (91,-3), (56,1), (35,-1)], 4⟩,
    ⟨4, 7, 35, 61, [(35,-1), (56,1), (91,-3), (30,-1), (37,-1), (58,1), (32,-1), (53,1), (60,1), (27,-3), (34,-1), (55,1), (62,1), (29,-1), (36,-1), (57,1), (64,3), (31,-1), (38,-1), (59,1), (33,-1), (54,1), (61,1)], 4⟩,
    ⟨35, 61, 31, 54, [(61,1), (35,-1), (56,1), (30,-1), (91,-3), (37,-1), (58,1), (32,-1), (53,1), (60,1), (27,-3), (34,-1), (55,1), (62,1), (29,-1), (36,-1), (57,1), (64,3), (31,-1), (38,-1), (59,1), (33,-1), (54,1)], 4⟩,
    ⟨31, 54, 19, 33, [(54,1), (61,1), (35,-1), (56,1), (30,-1), (37,-1), (91,-3), (58,1), (32,-1), (53,1), (60,1), (27,-3), (34,-1), (55,1), (62,1), (29,-1), (36,-1), (57,1), (64,3), (31,-1), (38,-1), (59,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment147_checked : phiCertifiedSegment147.check=true := by decide +kernel

def phiCertifiedSegment148 : PhiCertifiedSegment :=
  ⟨(19/33), (15/26), 5, [
    ⟨19, 33, 34, 59, [(33,-1), (54,1), (61,1), (35,-1), (56,1), (30,-1), (37,-1), (58,1), (91,-3), (32,-1), (53,1), (27,-3), (60,1), (34,-1), (55,1), (29,-1), (62,1), (36,-1), (57,1), (31,-1), (64,3), (38,-1), (59,1)], 5⟩,
    ⟨34, 59, 15, 26, [(59,1), (33,-1), (54,1), (61,1), (35,-1), (56,1), (30,-1), (37,-1), (58,1), (32,-1), (91,-3), (53,1), (27,-3), (60,1), (34,-1), (55,1), (29,-1), (62,1), (36,-1), (57,1), (31,-1), (64,3), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment148_checked : phiCertifiedSegment148.check=true := by decide +kernel

def phiCertifiedSegment149 : PhiCertifiedSegment :=
  ⟨(15/26), (18/31), 4, [
    ⟨15, 26, 37, 64, [(33,-1), (59,1), (54,1), (35,-1), (61,1), (30,-1), (56,1), (37,-1), (32,-1), (58,1), (91,-3), (27,-3), (53,1), (34,-1), (60,1), (29,-1), (55,1), (36,-1), (62,1), (31,-1), (57,1), (38,-1), (64,3)], 4⟩,
    ⟨37, 64, 11, 19, [(64,3), (33,-1), (59,1), (54,1), (35,-1), (61,1), (30,-1), (56,1), (37,-1), (32,-1), (58,1), (27,-3), (91,-3), (53,1), (34,-1), (60,1), (29,-1), (55,1), (36,-1), (62,1), (31,-1), (57,1), (38,-1)], 4⟩,
    ⟨11, 19, 18, 31, [(38,-1), (57,1), (64,3), (33,-1), (59,1), (35,-1), (54,1), (61,1), (30,-1), (37,-1), (56,1), (32,-1), (58,1), (27,-3), (34,-1), (53,1), (91,-3), (60,1), (29,-1), (36,-1), (55,1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment149_checked : phiCertifiedSegment149.check=true := by decide +kernel

def phiCertifiedSegment150 : PhiCertifiedSegment :=
  ⟨(18/31), (53/91), 5, [
    ⟨18, 31, 32, 55, [(31,-1), (62,1), (38,-1), (57,1), (33,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (58,1), (34,-1), (53,1), (29,-1), (60,1), (91,-3), (36,-1), (55,1)], 5⟩,
    ⟨32, 55, 53, 91, [(55,1), (31,-1), (62,1), (38,-1), (57,1), (33,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (58,1), (34,-1), (53,1), (29,-1), (60,1), (36,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment150_checked : phiCertifiedSegment150.check=true := by decide +kernel

def phiCertifiedSegment151 : PhiCertifiedSegment :=
  ⟨(53/91), (7/12), 8, [
    ⟨53, 91, 7, 12, [(91,-3), (55,1), (31,-1), (62,1), (38,-1), (57,1), (33,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (58,1), (34,-1), (53,1), (29,-1), (60,1), (36,-1)], 8⟩]⟩

lemma phiCertifiedSegment151_checked : phiCertifiedSegment151.check=true := by decide +kernel

def phiCertifiedSegment152 : PhiCertifiedSegment :=
  ⟨(7/12), (17/29), 7, [
    ⟨7, 12, 31, 53, [(36,-1), (60,1), (31,-1), (55,1), (91,-3), (38,-1), (62,1), (33,-1), (57,1), (64,3), (35,-1), (59,1), (30,-1), (54,1), (37,-1), (61,1), (32,-1), (56,1), (27,-3), (34,-1), (58,1), (29,-1), (53,1)], 7⟩,
    ⟨31, 53, 17, 29, [(53,1), (36,-1), (60,1), (31,-1), (55,1), (38,-1), (91,-3), (62,1), (33,-1), (57,1), (64,3), (35,-1), (59,1), (30,-1), (54,1), (37,-1), (61,1), (32,-1), (56,1), (27,-3), (34,-1), (58,1), (29,-1)], 7⟩]⟩

lemma phiCertifiedSegment152_checked : phiCertifiedSegment152.check=true := by decide +kernel

def phiCertifiedSegment153 : PhiCertifiedSegment :=
  ⟨(17/29), (16/27), 8, [
    ⟨17, 29, 10, 17, [(29,-1), (58,1), (53,1), (36,-1), (31,-1), (60,1), (55,1), (38,-1), (33,-1), (62,1), (91,-3), (57,1), (35,-1), (64,3), (30,-1), (59,1), (54,1), (37,-1), (32,-1), (61,1), (27,-3), (56,1), (34,-1)], 8⟩,
    ⟨10, 17, 33, 56, [(34,-1), (29,-1), (58,1), (36,-1), (53,1), (31,-1), (60,1), (38,-1), (55,1), (33,-1), (62,1), (57,1), (91,-3), (35,-1), (30,-1), (64,3), (59,1), (37,-1), (54,1), (32,-1), (27,-3), (61,1), (56,1)], 8⟩,
    ⟨33, 56, 36, 61, [(56,1), (34,-1), (29,-1), (58,1), (36,-1), (53,1), (31,-1), (60,1), (38,-1), (55,1), (33,-1), (62,1), (57,1), (35,-1), (91,-3), (30,-1), (64,3), (59,1), (37,-1), (54,1), (32,-1), (27,-3), (61,1)], 8⟩,
    ⟨36, 61, 13, 22, [(61,1), (56,1), (34,-1), (29,-1), (58,1), (36,-1), (53,1), (31,-1), (60,1), (38,-1), (55,1), (33,-1), (62,1), (57,1), (35,-1), (30,-1), (91,-3), (64,3), (59,1), (37,-1), (54,1), (32,-1), (27,-3)], 8⟩,
    ⟨13, 22, 16, 27, [(61,1), (34,-1), (56,1), (29,-1), (36,-1), (58,1), (31,-1), (53,1), (38,-1), (60,1), (33,-1), (55,1), (62,1), (35,-1), (57,1), (30,-1), (91,-3), (64,3), (37,-1), (59,1), (32,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment153_checked : phiCertifiedSegment153.check=true := by decide +kernel

def phiCertifiedSegment154 : PhiCertifiedSegment :=
  ⟨(16/27), (20/33), 4, [
    ⟨16, 27, 35, 59, [(27,-3), (54,1), (34,-1), (61,1), (29,-1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (62,1), (30,-1), (57,1), (37,-1), (64,3), (91,-3), (32,-1), (59,1)], 4⟩,
    ⟨35, 59, 54, 91, [(59,1), (27,-3), (54,1), (34,-1), (61,1), (29,-1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (62,1), (30,-1), (57,1), (37,-1), (64,3), (32,-1), (91,-3)], 4⟩,
    ⟨54, 91, 19, 32, [(91,-3), (59,1), (27,-3), (54,1), (34,-1), (61,1), (29,-1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (62,1), (30,-1), (57,1), (37,-1), (64,3), (32,-1)], 4⟩,
    ⟨19, 32, 22, 37, [(32,-1), (64,3), (27,-3), (59,1), (91,-3), (54,1), (34,-1), (29,-1), (61,1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (30,-1), (62,1), (57,1), (37,-1)], 4⟩,
    ⟨22, 37, 34, 57, [(37,-1), (32,-1), (27,-3), (64,3), (59,1), (54,1), (91,-3), (34,-1), (29,-1), (61,1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (30,-1), (62,1), (57,1)], 4⟩,
    ⟨34, 57, 37, 62, [(57,1), (37,-1), (32,-1), (27,-3), (64,3), (59,1), (54,1), (34,-1), (91,-3), (29,-1), (61,1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (30,-1), (62,1)], 4⟩,
    ⟨37, 62, 3, 5, [(62,1), (57,1), (37,-1), (32,-1), (27,-3), (64,3), (59,1), (54,1), (34,-1), (29,-1), (91,-3), (61,1), (56,1), (36,-1), (31,-1), (58,1), (53,1), (38,-1), (33,-1), (60,1), (55,1), (35,-1), (30,-1)], 4⟩,
    ⟨3, 5, 35, 58, [(30,-1), (35,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (56,1), (61,1), (91,-3), (33,-1), (38,-1), (53,1), (58,1)], 4⟩,
    ⟨35, 58, 32, 53, [(58,1), (30,-1), (35,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (56,1), (61,1), (33,-1), (91,-3), (38,-1), (53,1)], 4⟩,
    ⟨32, 53, 55, 91, [(53,1), (58,1), (30,-1), (35,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (56,1), (61,1), (33,-1), (38,-1), (91,-3)], 4⟩,
    ⟨55, 91, 23, 38, [(91,-3), (53,1), (58,1), (30,-1), (35,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (56,1), (61,1), (33,-1), (38,-1)], 4⟩,
    ⟨23, 38, 20, 33, [(38,-1), (53,1), (91,-3), (58,1), (30,-1), (35,-1), (55,1), (60,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (31,-1), (36,-1), (56,1), (61,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment154_checked : phiCertifiedSegment154.check=true := by decide +kernel

def phiCertifiedSegment155 : PhiCertifiedSegment :=
  ⟨(20/33), (17/28), 5, [
    ⟨20, 33, 37, 61, [(33,-1), (38,-1), (53,1), (58,1), (91,-3), (30,-1), (35,-1), (55,1), (27,-3), (60,1), (32,-1), (37,-1), (57,1), (29,-1), (62,1), (34,-1), (54,1), (59,1), (31,-1), (64,3), (36,-1), (56,1), (61,1)], 5⟩,
    ⟨37, 61, 17, 28, [(61,1), (33,-1), (38,-1), (53,1), (58,1), (30,-1), (91,-3), (35,-1), (55,1), (27,-3), (60,1), (32,-1), (37,-1), (57,1), (29,-1), (62,1), (34,-1), (54,1), (59,1), (31,-1), (64,3), (36,-1), (56,1)], 5⟩]⟩

lemma phiCertifiedSegment155_checked : phiCertifiedSegment155.check=true := by decide +kernel

def phiCertifiedSegment156 : PhiCertifiedSegment :=
  ⟨(17/28), (19/31), 4, [
    ⟨17, 28, 14, 23, [(56,1), (33,-1), (61,1), (38,-1), (53,1), (30,-1), (58,1), (35,-1), (91,-3), (27,-3), (55,1), (32,-1), (60,1), (37,-1), (29,-1), (57,1), (34,-1), (62,1), (54,1), (31,-1), (59,1), (36,-1), (64,3)], 4⟩,
    ⟨14, 23, 39, 64, [(33,-1), (56,1), (38,-1), (61,1), (30,-1), (53,1), (35,-1), (58,1), (91,-3), (27,-3), (32,-1), (55,1), (37,-1), (60,1), (29,-1), (34,-1), (57,1), (62,1), (31,-1), (54,1), (36,-1), (59,1), (64,3)], 4⟩,
    ⟨39, 64, 36, 59, [(64,3), (33,-1), (56,1), (38,-1), (61,1), (30,-1), (53,1), (35,-1), (58,1), (27,-3), (91,-3), (32,-1), (55,1), (37,-1), (60,1), (29,-1), (34,-1), (57,1), (62,1), (31,-1), (54,1), (36,-1), (59,1)], 4⟩,
    ⟨36, 59, 11, 18, [(59,1), (64,3), (33,-1), (56,1), (38,-1), (61,1), (30,-1), (53,1), (35,-1), (58,1), (27,-3), (32,-1), (91,-3), (55,1), (37,-1), (60,1), (29,-1), (34,-1), (57,1), (62,1), (31,-1), (54,1), (36,-1)], 4⟩,
    ⟨11, 18, 19, 31, [(36,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (56,1), (61,1), (30,-1), (35,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (55,1), (91,-3), (60,1), (29,-1), (34,-1), (57,1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment156_checked : phiCertifiedSegment156.check=true := by decide +kernel

def phiCertifiedSegment157 : PhiCertifiedSegment :=
  ⟨(19/31), (8/13), 5, [
    ⟨19, 31, 35, 57, [(31,-1), (62,1), (36,-1), (54,1), (59,1), (33,-1), (64,3), (38,-1), (56,1), (30,-1), (61,1), (35,-1), (53,1), (27,-3), (58,1), (32,-1), (37,-1), (55,1), (29,-1), (60,1), (91,-3), (34,-1), (57,1)], 5⟩,
    ⟨35, 57, 8, 13, [(57,1), (31,-1), (62,1), (36,-1), (54,1), (59,1), (33,-1), (64,3), (38,-1), (56,1), (30,-1), (61,1), (35,-1), (53,1), (27,-3), (58,1), (32,-1), (37,-1), (55,1), (29,-1), (60,1), (34,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment157_checked : phiCertifiedSegment157.check=true := by decide +kernel

def phiCertifiedSegment158 : PhiCertifiedSegment :=
  ⟨(8/13), (13/21), 7, [
    ⟨8, 13, 37, 60, [(91,-3), (31,-1), (57,1), (36,-1), (62,1), (54,1), (33,-1), (59,1), (38,-1), (64,3), (30,-1), (56,1), (35,-1), (61,1), (27,-3), (53,1), (32,-1), (58,1), (37,-1), (29,-1), (55,1), (34,-1), (60,1)], 7⟩,
    ⟨37, 60, 21, 34, [(60,1), (31,-1), (91,-3), (57,1), (36,-1), (62,1), (54,1), (33,-1), (59,1), (38,-1), (64,3), (30,-1), (56,1), (35,-1), (61,1), (27,-3), (53,1), (32,-1), (58,1), (37,-1), (29,-1), (55,1), (34,-1)], 7⟩,
    ⟨21, 34, 34, 55, [(34,-1), (60,1), (31,-1), (57,1), (91,-3), (36,-1), (62,1), (54,1), (33,-1), (59,1), (38,-1), (30,-1), (64,3), (56,1), (35,-1), (27,-3), (61,1), (53,1), (32,-1), (58,1), (37,-1), (29,-1), (55,1)], 7⟩,
    ⟨34, 55, 13, 21, [(55,1), (34,-1), (60,1), (31,-1), (57,1), (36,-1), (91,-3), (62,1), (54,1), (33,-1), (59,1), (38,-1), (30,-1), (64,3), (56,1), (35,-1), (27,-3), (61,1), (53,1), (32,-1), (58,1), (37,-1), (29,-1)], 7⟩]⟩

lemma phiCertifiedSegment158_checked : phiCertifiedSegment158.check=true := by decide +kernel

def phiCertifiedSegment159 : PhiCertifiedSegment :=
  ⟨(13/21), (23/37), 8, [
    ⟨13, 21, 18, 29, [(34,-1), (55,1), (60,1), (31,-1), (36,-1), (57,1), (91,-3), (62,1), (33,-1), (54,1), (38,-1), (59,1), (30,-1), (64,3), (35,-1), (56,1), (27,-3), (61,1), (32,-1), (53,1), (37,-1), (58,1), (29,-1)], 8⟩,
    ⟨18, 29, 23, 37, [(29,-1), (58,1), (34,-1), (55,1), (31,-1), (60,1), (36,-1), (57,1), (33,-1), (62,1), (91,-3), (54,1), (38,-1), (30,-1), (59,1), (35,-1), (64,3), (27,-3), (56,1), (32,-1), (61,1), (53,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment159_checked : phiCertifiedSegment159.check=true := by decide +kernel

def phiCertifiedSegment160 : PhiCertifiedSegment :=
  ⟨(23/37), (57/91), 5, [
    ⟨23, 37, 33, 53, [(37,-1), (29,-1), (58,1), (34,-1), (55,1), (31,-1), (60,1), (36,-1), (57,1), (33,-1), (62,1), (54,1), (91,-3), (38,-1), (30,-1), (59,1), (35,-1), (27,-3), (64,3), (56,1), (32,-1), (61,1), (53,1)], 5⟩,
    ⟨33, 53, 38, 61, [(53,1), (37,-1), (29,-1), (58,1), (34,-1), (55,1), (31,-1), (60,1), (36,-1), (57,1), (33,-1), (62,1), (54,1), (38,-1), (91,-3), (30,-1), (59,1), (35,-1), (27,-3), (64,3), (56,1), (32,-1), (61,1)], 5⟩,
    ⟨38, 61, 5, 8, [(61,1), (53,1), (37,-1), (29,-1), (58,1), (34,-1), (55,1), (31,-1), (60,1), (36,-1), (57,1), (33,-1), (62,1), (54,1), (38,-1), (30,-1), (91,-3), (59,1), (35,-1), (27,-3), (64,3), (56,1), (32,-1)], 5⟩,
    ⟨5, 8, 57, 91, [(32,-1), (56,1), (64,3), (29,-1), (37,-1), (53,1), (61,1), (34,-1), (58,1), (31,-1), (55,1), (36,-1), (60,1), (33,-1), (57,1), (30,-1), (38,-1), (54,1), (62,1), (27,-3), (35,-1), (59,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment160_checked : phiCertifiedSegment160.check=true := by decide +kernel

def phiCertifiedSegment161 : PhiCertifiedSegment :=
  ⟨(57/91), (17/27), 7, [
    ⟨57, 91, 37, 59, [(91,-3), (32,-1), (56,1), (64,3), (29,-1), (37,-1), (53,1), (61,1), (34,-1), (58,1), (31,-1), (55,1), (36,-1), (60,1), (33,-1), (57,1), (30,-1), (38,-1), (54,1), (62,1), (27,-3), (35,-1), (59,1)], 7⟩,
    ⟨37, 59, 22, 35, [(59,1), (32,-1), (91,-3), (56,1), (64,3), (29,-1), (37,-1), (53,1), (61,1), (34,-1), (58,1), (31,-1), (55,1), (36,-1), (60,1), (33,-1), (57,1), (30,-1), (38,-1), (54,1), (62,1), (27,-3), (35,-1)], 7⟩,
    ⟨22, 35, 39, 62, [(35,-1), (59,1), (32,-1), (56,1), (91,-3), (29,-1), (64,3), (37,-1), (53,1), (61,1), (34,-1), (58,1), (31,-1), (55,1), (36,-1), (60,1), (33,-1), (57,1), (30,-1), (38,-1), (54,1), (27,-3), (62,1)], 7⟩,
    ⟨39, 62, 17, 27, [(62,1), (35,-1), (59,1), (32,-1), (56,1), (29,-1), (91,-3), (64,3), (37,-1), (53,1), (61,1), (34,-1), (58,1), (31,-1), (55,1), (36,-1), (60,1), (33,-1), (57,1), (30,-1), (38,-1), (54,1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment161_checked : phiCertifiedSegment161.check=true := by decide +kernel

def phiCertifiedSegment162 : PhiCertifiedSegment :=
  ⟨(17/27), (9/14), 4, [
    ⟨17, 27, 12, 19, [(27,-3), (54,1), (35,-1), (62,1), (32,-1), (59,1), (29,-1), (56,1), (37,-1), (64,3), (91,-3), (53,1), (34,-1), (61,1), (31,-1), (58,1), (55,1), (36,-1), (33,-1), (60,1), (30,-1), (57,1), (38,-1)], 4⟩,
    ⟨12, 19, 19, 30, [(38,-1), (57,1), (27,-3), (35,-1), (54,1), (62,1), (32,-1), (59,1), (29,-1), (37,-1), (56,1), (64,3), (34,-1), (53,1), (91,-3), (61,1), (31,-1), (58,1), (36,-1), (55,1), (33,-1), (60,1), (30,-1)], 4⟩,
    ⟨19, 30, 7, 11, [(30,-1), (60,1), (38,-1), (27,-3), (57,1), (35,-1), (54,1), (32,-1), (62,1), (29,-1), (59,1), (37,-1), (56,1), (34,-1), (64,3), (53,1), (31,-1), (61,1), (91,-3), (58,1), (36,-1), (55,1), (33,-1)], 4⟩,
    ⟨7, 11, 58, 91, [(33,-1), (55,1), (30,-1), (27,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (64,3), (61,1), (36,-1), (58,1), (91,-3)], 4⟩,
    ⟨58, 91, 37, 58, [(91,-3), (33,-1), (55,1), (30,-1), (27,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (64,3), (61,1), (36,-1), (58,1)], 4⟩,
    ⟨37, 58, 23, 36, [(58,1), (33,-1), (91,-3), (55,1), (30,-1), (27,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (64,3), (61,1), (36,-1)], 4⟩,
    ⟨23, 36, 39, 61, [(36,-1), (58,1), (33,-1), (55,1), (91,-3), (30,-1), (27,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (64,3), (61,1)], 4⟩,
    ⟨39, 61, 16, 25, [(61,1), (36,-1), (58,1), (33,-1), (55,1), (30,-1), (91,-3), (27,-3), (38,-1), (60,1), (35,-1), (57,1), (32,-1), (54,1), (29,-1), (62,1), (37,-1), (59,1), (34,-1), (56,1), (31,-1), (53,1), (64,3)], 4⟩,
    ⟨16, 25, 41, 64, [(36,-1), (61,1), (33,-1), (58,1), (30,-1), (55,1), (91,-3), (27,-3), (38,-1), (35,-1), (60,1), (32,-1), (57,1), (29,-1), (54,1), (37,-1), (62,1), (34,-1), (59,1), (31,-1), (56,1), (53,1), (64,3)], 4⟩,
    ⟨41, 64, 34, 53, [(64,3), (36,-1), (61,1), (33,-1), (58,1), (30,-1), (55,1), (27,-3), (91,-3), (38,-1), (35,-1), (60,1), (32,-1), (57,1), (29,-1), (54,1), (37,-1), (62,1), (34,-1), (59,1), (31,-1), (56,1), (53,1)], 4⟩,
    ⟨34, 53, 9, 14, [(53,1), (64,3), (36,-1), (61,1), (33,-1), (58,1), (30,-1), (55,1), (27,-3), (38,-1), (91,-3), (35,-1), (60,1), (32,-1), (57,1), (29,-1), (54,1), (37,-1), (62,1), (34,-1), (59,1), (31,-1), (56,1)], 4⟩]⟩

lemma phiCertifiedSegment162_checked : phiCertifiedSegment162.check=true := by decide +kernel

def phiCertifiedSegment163 : PhiCertifiedSegment :=
  ⟨(9/14), (20/31), 3, [
    ⟨9, 14, 38, 59, [(56,1), (53,1), (36,-1), (64,3), (33,-1), (61,1), (30,-1), (58,1), (27,-3), (55,1), (38,-1), (35,-1), (91,-3), (32,-1), (60,1), (29,-1), (57,1), (54,1), (37,-1), (34,-1), (62,1), (31,-1), (59,1)], 3⟩,
    ⟨38, 59, 20, 31, [(59,1), (56,1), (53,1), (36,-1), (64,3), (33,-1), (61,1), (30,-1), (58,1), (27,-3), (55,1), (38,-1), (35,-1), (32,-1), (91,-3), (60,1), (29,-1), (57,1), (54,1), (37,-1), (34,-1), (62,1), (31,-1)], 3⟩]⟩

lemma phiCertifiedSegment163_checked : phiCertifiedSegment163.check=true := by decide +kernel

def phiCertifiedSegment164 : PhiCertifiedSegment :=
  ⟨(20/31), (11/17), 4, [
    ⟨20, 31, 11, 17, [(31,-1), (62,1), (59,1), (56,1), (53,1), (36,-1), (33,-1), (64,3), (30,-1), (61,1), (27,-3), (58,1), (55,1), (38,-1), (35,-1), (32,-1), (29,-1), (60,1), (91,-3), (57,1), (54,1), (37,-1), (34,-1)], 4⟩]⟩

lemma phiCertifiedSegment164_checked : phiCertifiedSegment164.check=true := by decide +kernel

def phiCertifiedSegment165 : PhiCertifiedSegment :=
  ⟨(11/17), (59/91), 5, [
    ⟨11, 17, 35, 54, [(34,-1), (31,-1), (62,1), (59,1), (56,1), (36,-1), (53,1), (33,-1), (30,-1), (64,3), (27,-3), (61,1), (58,1), (38,-1), (55,1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (91,-3), (37,-1), (54,1)], 5⟩,
    ⟨35, 54, 59, 91, [(54,1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (36,-1), (53,1), (33,-1), (30,-1), (64,3), (27,-3), (61,1), (58,1), (38,-1), (55,1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (37,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment165_checked : phiCertifiedSegment165.check=true := by decide +kernel

def phiCertifiedSegment166 : PhiCertifiedSegment :=
  ⟨(59/91), (24/37), 7, [
    ⟨59, 91, 24, 37, [(91,-3), (54,1), (34,-1), (31,-1), (62,1), (59,1), (56,1), (36,-1), (53,1), (33,-1), (30,-1), (64,3), (27,-3), (61,1), (58,1), (38,-1), (55,1), (35,-1), (32,-1), (29,-1), (60,1), (57,1), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment166_checked : phiCertifiedSegment166.check=true := by decide +kernel

def phiCertifiedSegment167 : PhiCertifiedSegment :=
  ⟨(24/37), (15/23), 5, [
    ⟨24, 37, 37, 57, [(37,-1), (54,1), (91,-3), (34,-1), (31,-1), (62,1), (59,1), (56,1), (36,-1), (53,1), (33,-1), (30,-1), (27,-3), (64,3), (61,1), (58,1), (38,-1), (55,1), (35,-1), (32,-1), (29,-1), (60,1), (57,1)], 5⟩,
    ⟨37, 57, 13, 20, [(57,1), (37,-1), (54,1), (34,-1), (91,-3), (31,-1), (62,1), (59,1), (56,1), (36,-1), (53,1), (33,-1), (30,-1), (27,-3), (64,3), (61,1), (58,1), (38,-1), (55,1), (35,-1), (32,-1), (29,-1), (60,1)], 5⟩,
    ⟨13, 20, 15, 23, [(60,1), (37,-1), (57,1), (34,-1), (54,1), (31,-1), (91,-3), (62,1), (59,1), (36,-1), (56,1), (33,-1), (53,1), (30,-1), (27,-3), (64,3), (61,1), (38,-1), (58,1), (35,-1), (55,1), (32,-1), (29,-1)], 5⟩]⟩

lemma phiCertifiedSegment167_checked : phiCertifiedSegment167.check=true := by decide +kernel

def phiCertifiedSegment168 : PhiCertifiedSegment :=
  ⟨(15/23), (17/26), 6, [
    ⟨15, 23, 17, 26, [(37,-1), (60,1), (34,-1), (57,1), (31,-1), (54,1), (91,-3), (62,1), (36,-1), (59,1), (33,-1), (56,1), (30,-1), (53,1), (27,-3), (64,3), (38,-1), (61,1), (35,-1), (58,1), (32,-1), (55,1), (29,-1)], 6⟩]⟩

lemma phiCertifiedSegment168_checked : phiCertifiedSegment168.check=true := by decide +kernel

def phiCertifiedSegment169 : PhiCertifiedSegment :=
  ⟨(17/26), (23/35), 5, [
    ⟨17, 26, 36, 55, [(37,-1), (34,-1), (60,1), (31,-1), (57,1), (54,1), (91,-3), (36,-1), (62,1), (33,-1), (59,1), (30,-1), (56,1), (27,-3), (53,1), (38,-1), (64,3), (35,-1), (61,1), (32,-1), (58,1), (29,-1), (55,1)], 5⟩,
    ⟨36, 55, 19, 29, [(55,1), (37,-1), (34,-1), (60,1), (31,-1), (57,1), (54,1), (36,-1), (91,-3), (62,1), (33,-1), (59,1), (30,-1), (56,1), (27,-3), (53,1), (38,-1), (64,3), (35,-1), (61,1), (32,-1), (58,1), (29,-1)], 5⟩,
    ⟨19, 29, 40, 61, [(29,-1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (62,1), (91,-3), (30,-1), (59,1), (27,-3), (56,1), (53,1), (38,-1), (35,-1), (64,3), (32,-1), (61,1)], 5⟩,
    ⟨40, 61, 21, 32, [(61,1), (29,-1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (62,1), (30,-1), (91,-3), (59,1), (27,-3), (56,1), (53,1), (38,-1), (35,-1), (64,3), (32,-1)], 5⟩,
    ⟨21, 32, 23, 35, [(32,-1), (64,3), (29,-1), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (62,1), (27,-3), (59,1), (91,-3), (56,1), (53,1), (38,-1), (35,-1)], 5⟩]⟩

lemma phiCertifiedSegment169_checked : phiCertifiedSegment169.check=true := by decide +kernel

def phiCertifiedSegment170 : PhiCertifiedSegment :=
  ⟨(23/35), (2/3), 6, [
    ⟨23, 35, 25, 38, [(35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1), (91,-3), (53,1), (38,-1)], 6⟩,
    ⟨25, 38, 60, 91, [(38,-1), (35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1), (53,1), (91,-3)], 6⟩,
    ⟨60, 91, 35, 53, [(91,-3), (38,-1), (35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1), (53,1)], 6⟩,
    ⟨35, 53, 37, 56, [(53,1), (38,-1), (91,-3), (35,-1), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1), (56,1)], 6⟩,
    ⟨37, 56, 39, 59, [(56,1), (53,1), (38,-1), (35,-1), (91,-3), (32,-1), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1), (59,1)], 6⟩,
    ⟨39, 59, 41, 62, [(59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (91,-3), (29,-1), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3), (62,1)], 6⟩,
    ⟨41, 62, 2, 3, [(62,1), (59,1), (56,1), (53,1), (38,-1), (35,-1), (32,-1), (29,-1), (91,-3), (64,3), (61,1), (58,1), (55,1), (37,-1), (34,-1), (31,-1), (60,1), (57,1), (54,1), (36,-1), (33,-1), (30,-1), (27,-3)], 6⟩]⟩

lemma phiCertifiedSegment170_checked : phiCertifiedSegment170.check=true := by decide +kernel

def phiCertifiedSegment171 : PhiCertifiedSegment :=
  ⟨(2/3), (21/31), 3, [
    ⟨2, 3, 61, 91, [(27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3), (91,-3)], 3⟩,
    ⟨61, 91, 43, 64, [(91,-3), (27,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1), (64,3)], 3⟩,
    ⟨43, 64, 41, 61, [(64,3), (27,-3), (91,-3), (30,-1), (33,-1), (36,-1), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1), (61,1)], 3⟩,
    ⟨41, 61, 39, 58, [(61,1), (64,3), (27,-3), (30,-1), (91,-3), (33,-1), (36,-1), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1), (55,1), (58,1)], 3⟩,
    ⟨39, 58, 37, 55, [(58,1), (61,1), (64,3), (27,-3), (30,-1), (33,-1), (91,-3), (36,-1), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1), (55,1)], 3⟩,
    ⟨37, 55, 25, 37, [(55,1), (58,1), (61,1), (64,3), (27,-3), (30,-1), (33,-1), (36,-1), (91,-3), (54,1), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1), (37,-1)], 3⟩,
    ⟨25, 37, 23, 34, [(37,-1), (55,1), (58,1), (61,1), (27,-3), (64,3), (30,-1), (33,-1), (36,-1), (54,1), (91,-3), (57,1), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1), (34,-1)], 3⟩,
    ⟨23, 34, 21, 31, [(34,-1), (37,-1), (55,1), (58,1), (27,-3), (61,1), (30,-1), (64,3), (33,-1), (36,-1), (54,1), (57,1), (91,-3), (60,1), (29,-1), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1), (62,1), (31,-1)], 3⟩]⟩

lemma phiCertifiedSegment171_checked : phiCertifiedSegment171.check=true := by decide +kernel

def phiCertifiedSegment172 : PhiCertifiedSegment :=
  ⟨(21/31), (17/25), 4, [
    ⟨21, 31, 40, 59, [(31,-1), (62,1), (34,-1), (37,-1), (55,1), (27,-3), (58,1), (30,-1), (61,1), (33,-1), (64,3), (36,-1), (54,1), (57,1), (29,-1), (60,1), (91,-3), (32,-1), (35,-1), (38,-1), (53,1), (56,1), (59,1)], 4⟩,
    ⟨40, 59, 19, 28, [(59,1), (31,-1), (62,1), (34,-1), (37,-1), (55,1), (27,-3), (58,1), (30,-1), (61,1), (33,-1), (64,3), (36,-1), (54,1), (57,1), (29,-1), (60,1), (32,-1), (91,-3), (35,-1), (38,-1), (53,1), (56,1)], 4⟩,
    ⟨19, 28, 36, 53, [(56,1), (31,-1), (59,1), (34,-1), (62,1), (37,-1), (27,-3), (55,1), (30,-1), (58,1), (33,-1), (61,1), (36,-1), (64,3), (54,1), (29,-1), (57,1), (32,-1), (60,1), (35,-1), (91,-3), (38,-1), (53,1)], 4⟩,
    ⟨36, 53, 17, 25, [(53,1), (56,1), (31,-1), (59,1), (34,-1), (62,1), (37,-1), (27,-3), (55,1), (30,-1), (58,1), (33,-1), (61,1), (36,-1), (64,3), (54,1), (29,-1), (57,1), (32,-1), (60,1), (35,-1), (38,-1), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment172_checked : phiCertifiedSegment172.check=true := by decide +kernel

def phiCertifiedSegment173 : PhiCertifiedSegment :=
  ⟨(17/25), (15/22), 5, [
    ⟨17, 25, 62, 91, [(53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (27,-3), (30,-1), (55,1), (33,-1), (58,1), (36,-1), (61,1), (64,3), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1), (91,-3)], 5⟩,
    ⟨62, 91, 15, 22, [(91,-3), (53,1), (31,-1), (56,1), (34,-1), (59,1), (37,-1), (62,1), (27,-3), (30,-1), (55,1), (33,-1), (58,1), (36,-1), (61,1), (64,3), (29,-1), (54,1), (32,-1), (57,1), (35,-1), (60,1), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment173_checked : phiCertifiedSegment173.check=true := by decide +kernel

def phiCertifiedSegment174 : PhiCertifiedSegment :=
  ⟨(15/22), (20/29), 4, [
    ⟨15, 22, 41, 60, [(91,-3), (31,-1), (53,1), (34,-1), (56,1), (37,-1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (55,1), (36,-1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (54,1), (35,-1), (57,1), (38,-1), (60,1)], 4⟩,
    ⟨41, 60, 13, 19, [(60,1), (31,-1), (91,-3), (53,1), (34,-1), (56,1), (37,-1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (55,1), (36,-1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (54,1), (35,-1), (57,1), (38,-1)], 4⟩,
    ⟨13, 19, 37, 54, [(38,-1), (57,1), (60,1), (31,-1), (34,-1), (53,1), (91,-3), (37,-1), (56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1), (54,1)], 4⟩,
    ⟨37, 54, 24, 35, [(54,1), (38,-1), (57,1), (60,1), (31,-1), (34,-1), (53,1), (37,-1), (91,-3), (56,1), (59,1), (62,1), (27,-3), (30,-1), (33,-1), (36,-1), (55,1), (58,1), (61,1), (64,3), (29,-1), (32,-1), (35,-1)], 4⟩,
    ⟨24, 35, 11, 16, [(35,-1), (54,1), (38,-1), (57,1), (60,1), (31,-1), (34,-1), (53,1), (37,-1), (56,1), (91,-3), (59,1), (27,-3), (62,1), (30,-1), (33,-1), (36,-1), (55,1), (58,1), (61,1), (29,-1), (64,3), (32,-1)], 4⟩,
    ⟨11, 16, 42, 61, [(32,-1), (64,3), (35,-1), (38,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (53,1), (56,1), (27,-3), (59,1), (91,-3), (30,-1), (62,1), (33,-1), (36,-1), (55,1), (58,1), (29,-1), (61,1)], 4⟩,
    ⟨42, 61, 20, 29, [(61,1), (32,-1), (64,3), (35,-1), (38,-1), (54,1), (57,1), (60,1), (31,-1), (34,-1), (37,-1), (53,1), (56,1), (27,-3), (59,1), (30,-1), (91,-3), (62,1), (33,-1), (36,-1), (55,1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment174_checked : phiCertifiedSegment174.check=true := by decide +kernel

def phiCertifiedSegment175 : PhiCertifiedSegment :=
  ⟨(20/29), (9/13), 5, [
    ⟨20, 29, 38, 55, [(29,-1), (58,1), (32,-1), (61,1), (35,-1), (64,3), (38,-1), (54,1), (57,1), (31,-1), (60,1), (34,-1), (37,-1), (53,1), (27,-3), (56,1), (30,-1), (59,1), (33,-1), (62,1), (91,-3), (36,-1), (55,1)], 5⟩,
    ⟨38, 55, 9, 13, [(55,1), (29,-1), (58,1), (32,-1), (61,1), (35,-1), (64,3), (38,-1), (54,1), (57,1), (31,-1), (60,1), (34,-1), (37,-1), (53,1), (27,-3), (56,1), (30,-1), (59,1), (33,-1), (62,1), (36,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment175_checked : phiCertifiedSegment175.check=true := by decide +kernel

def phiCertifiedSegment176 : PhiCertifiedSegment :=
  ⟨(9/13), (23/33), 7, [
    ⟨9, 13, 43, 62, [(91,-3), (29,-1), (55,1), (32,-1), (58,1), (35,-1), (61,1), (38,-1), (64,3), (54,1), (31,-1), (57,1), (34,-1), (60,1), (37,-1), (27,-3), (53,1), (30,-1), (56,1), (33,-1), (59,1), (36,-1), (62,1)], 7⟩,
    ⟨43, 62, 25, 36, [(62,1), (29,-1), (91,-3), (55,1), (32,-1), (58,1), (35,-1), (61,1), (38,-1), (64,3), (54,1), (31,-1), (57,1), (34,-1), (60,1), (37,-1), (27,-3), (53,1), (30,-1), (56,1), (33,-1), (59,1), (36,-1)], 7⟩,
    ⟨25, 36, 41, 59, [(36,-1), (62,1), (29,-1), (55,1), (91,-3), (32,-1), (58,1), (35,-1), (61,1), (38,-1), (64,3), (54,1), (31,-1), (57,1), (34,-1), (60,1), (37,-1), (27,-3), (53,1), (30,-1), (56,1), (33,-1), (59,1)], 7⟩,
    ⟨41, 59, 16, 23, [(59,1), (36,-1), (62,1), (29,-1), (55,1), (32,-1), (91,-3), (58,1), (35,-1), (61,1), (38,-1), (64,3), (54,1), (31,-1), (57,1), (34,-1), (60,1), (37,-1), (27,-3), (53,1), (30,-1), (56,1), (33,-1)], 7⟩,
    ⟨16, 23, 39, 56, [(36,-1), (59,1), (62,1), (29,-1), (32,-1), (55,1), (91,-3), (35,-1), (58,1), (38,-1), (61,1), (64,3), (31,-1), (54,1), (34,-1), (57,1), (37,-1), (60,1), (27,-3), (30,-1), (53,1), (33,-1), (56,1)], 7⟩,
    ⟨39, 56, 23, 33, [(56,1), (36,-1), (59,1), (62,1), (29,-1), (32,-1), (55,1), (35,-1), (91,-3), (58,1), (38,-1), (61,1), (64,3), (31,-1), (54,1), (34,-1), (57,1), (37,-1), (60,1), (27,-3), (30,-1), (53,1), (33,-1)], 7⟩]⟩

lemma phiCertifiedSegment176_checked : phiCertifiedSegment176.check=true := by decide +kernel

def phiCertifiedSegment177 : PhiCertifiedSegment :=
  ⟨(23/33), (7/10), 8, [
    ⟨23, 33, 37, 53, [(33,-1), (56,1), (36,-1), (59,1), (29,-1), (62,1), (32,-1), (55,1), (35,-1), (58,1), (91,-3), (38,-1), (61,1), (31,-1), (64,3), (54,1), (34,-1), (57,1), (37,-1), (27,-3), (60,1), (30,-1), (53,1)], 8⟩,
    ⟨37, 53, 7, 10, [(53,1), (33,-1), (56,1), (36,-1), (59,1), (29,-1), (62,1), (32,-1), (55,1), (35,-1), (58,1), (38,-1), (91,-3), (61,1), (31,-1), (64,3), (54,1), (34,-1), (57,1), (37,-1), (27,-3), (60,1), (30,-1)], 8⟩]⟩

lemma phiCertifiedSegment177_checked : phiCertifiedSegment177.check=true := by decide +kernel

def phiCertifiedSegment178 : PhiCertifiedSegment :=
  ⟨(7/10), (26/37), 7, [
    ⟨7, 10, 40, 57, [(30,-1), (60,1), (33,-1), (53,1), (36,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (55,1), (38,-1), (58,1), (31,-1), (61,1), (91,-3), (34,-1), (54,1), (64,3), (27,-3), (37,-1), (57,1)], 7⟩,
    ⟨40, 57, 26, 37, [(57,1), (30,-1), (60,1), (33,-1), (53,1), (36,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (55,1), (38,-1), (58,1), (31,-1), (61,1), (34,-1), (91,-3), (54,1), (64,3), (27,-3), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment178_checked : phiCertifiedSegment178.check=true := by decide +kernel

def phiCertifiedSegment179 : PhiCertifiedSegment :=
  ⟨(26/37), (64/91), 5, [
    ⟨26, 37, 45, 64, [(37,-1), (57,1), (30,-1), (60,1), (33,-1), (53,1), (36,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (55,1), (38,-1), (58,1), (31,-1), (61,1), (34,-1), (54,1), (91,-3), (27,-3), (64,3)], 5⟩,
    ⟨45, 64, 64, 91, [(64,3), (37,-1), (57,1), (30,-1), (60,1), (33,-1), (53,1), (36,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (55,1), (38,-1), (58,1), (31,-1), (61,1), (34,-1), (54,1), (27,-3), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment179_checked : phiCertifiedSegment179.check=true := by decide +kernel

def phiCertifiedSegment180 : PhiCertifiedSegment :=
  ⟨(64/91), (19/27), 8, [
    ⟨64, 91, 19, 27, [(91,-3), (64,3), (37,-1), (57,1), (30,-1), (60,1), (33,-1), (53,1), (36,-1), (56,1), (29,-1), (59,1), (32,-1), (62,1), (35,-1), (55,1), (38,-1), (58,1), (31,-1), (61,1), (34,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment180_checked : phiCertifiedSegment180.check=true := by decide +kernel

def phiCertifiedSegment181 : PhiCertifiedSegment :=
  ⟨(19/27), (12/17), 4, [
    ⟨19, 27, 43, 61, [(27,-3), (54,1), (37,-1), (64,3), (91,-3), (30,-1), (57,1), (33,-1), (60,1), (53,1), (36,-1), (29,-1), (56,1), (32,-1), (59,1), (35,-1), (62,1), (55,1), (38,-1), (31,-1), (58,1), (34,-1), (61,1)], 4⟩,
    ⟨43, 61, 12, 17, [(61,1), (27,-3), (54,1), (37,-1), (64,3), (30,-1), (91,-3), (57,1), (33,-1), (60,1), (53,1), (36,-1), (29,-1), (56,1), (32,-1), (59,1), (35,-1), (62,1), (55,1), (38,-1), (31,-1), (58,1), (34,-1)], 4⟩]⟩

lemma phiCertifiedSegment181_checked : phiCertifiedSegment181.check=true := by decide +kernel

def phiCertifiedSegment182 : PhiCertifiedSegment :=
  ⟨(12/17), (17/24), 5, [
    ⟨12, 17, 41, 58, [(34,-1), (27,-3), (61,1), (37,-1), (54,1), (30,-1), (64,3), (57,1), (91,-3), (33,-1), (60,1), (36,-1), (53,1), (29,-1), (56,1), (32,-1), (59,1), (35,-1), (62,1), (38,-1), (55,1), (31,-1), (58,1)], 5⟩,
    ⟨41, 58, 17, 24, [(58,1), (34,-1), (27,-3), (61,1), (37,-1), (54,1), (30,-1), (64,3), (57,1), (33,-1), (91,-3), (60,1), (36,-1), (53,1), (29,-1), (56,1), (32,-1), (59,1), (35,-1), (62,1), (38,-1), (55,1), (31,-1)], 5⟩]⟩

lemma phiCertifiedSegment182_checked : phiCertifiedSegment182.check=true := by decide +kernel

def phiCertifiedSegment183 : PhiCertifiedSegment :=
  ⟨(17/24), (21/29), 4, [
    ⟨17, 24, 39, 55, [(34,-1), (58,1), (27,-3), (37,-1), (61,1), (30,-1), (54,1), (64,3), (33,-1), (57,1), (91,-3), (36,-1), (60,1), (29,-1), (53,1), (32,-1), (56,1), (35,-1), (59,1), (38,-1), (62,1), (31,-1), (55,1)], 4⟩,
    ⟨39, 55, 22, 31, [(55,1), (34,-1), (58,1), (27,-3), (37,-1), (61,1), (30,-1), (54,1), (64,3), (33,-1), (57,1), (36,-1), (91,-3), (60,1), (29,-1), (53,1), (32,-1), (56,1), (35,-1), (59,1), (38,-1), (62,1), (31,-1)], 4⟩,
    ⟨22, 31, 27, 38, [(31,-1), (62,1), (55,1), (34,-1), (27,-3), (58,1), (37,-1), (30,-1), (61,1), (54,1), (33,-1), (64,3), (57,1), (36,-1), (29,-1), (60,1), (91,-3), (53,1), (32,-1), (56,1), (35,-1), (59,1), (38,-1)], 4⟩,
    ⟨27, 38, 42, 59, [(38,-1), (31,-1), (62,1), (55,1), (34,-1), (27,-3), (58,1), (37,-1), (30,-1), (61,1), (54,1), (33,-1), (64,3), (57,1), (36,-1), (29,-1), (60,1), (53,1), (91,-3), (32,-1), (56,1), (35,-1), (59,1)], 4⟩,
    ⟨42, 59, 5, 7, [(59,1), (38,-1), (31,-1), (62,1), (55,1), (34,-1), (27,-3), (58,1), (37,-1), (30,-1), (61,1), (54,1), (33,-1), (64,3), (57,1), (36,-1), (29,-1), (60,1), (53,1), (32,-1), (91,-3), (56,1), (35,-1)], 4⟩,
    ⟨5, 7, 43, 60, [(35,-1), (56,1), (91,-3), (31,-1), (38,-1), (59,1), (27,-3), (34,-1), (55,1), (62,1), (30,-1), (37,-1), (58,1), (33,-1), (54,1), (61,1), (29,-1), (36,-1), (57,1), (64,3), (32,-1), (53,1), (60,1)], 4⟩,
    ⟨43, 60, 38, 53, [(60,1), (35,-1), (56,1), (31,-1), (91,-3), (38,-1), (59,1), (27,-3), (34,-1), (55,1), (62,1), (30,-1), (37,-1), (58,1), (33,-1), (54,1), (61,1), (29,-1), (36,-1), (57,1), (64,3), (32,-1), (53,1)], 4⟩,
    ⟨38, 53, 23, 32, [(53,1), (60,1), (35,-1), (56,1), (31,-1), (38,-1), (91,-3), (59,1), (27,-3), (34,-1), (55,1), (62,1), (30,-1), (37,-1), (58,1), (33,-1), (54,1), (61,1), (29,-1), (36,-1), (57,1), (64,3), (32,-1)], 4⟩,
    ⟨23, 32, 41, 57, [(32,-1), (64,3), (53,1), (60,1), (35,-1), (56,1), (31,-1), (38,-1), (27,-3), (59,1), (91,-3), (34,-1), (55,1), (30,-1), (62,1), (37,-1), (58,1), (33,-1), (54,1), (29,-1), (61,1), (36,-1), (57,1)], 4⟩,
    ⟨41, 57, 18, 25, [(57,1), (32,-1), (64,3), (53,1), (60,1), (35,-1), (56,1), (31,-1), (38,-1), (27,-3), (59,1), (34,-1), (91,-3), (55,1), (30,-1), (62,1), (37,-1), (58,1), (33,-1), (54,1), (29,-1), (61,1), (36,-1)], 4⟩,
    ⟨18, 25, 44, 61, [(32,-1), (57,1), (64,3), (53,1), (35,-1), (60,1), (31,-1), (56,1), (38,-1), (27,-3), (34,-1), (59,1), (91,-3), (30,-1), (55,1), (37,-1), (62,1), (33,-1), (58,1), (29,-1), (54,1), (36,-1), (61,1)], 4⟩,
    ⟨44, 61, 13, 18, [(61,1), (32,-1), (57,1), (64,3), (53,1), (35,-1), (60,1), (31,-1), (56,1), (38,-1), (27,-3), (34,-1), (59,1), (30,-1), (91,-3), (55,1), (37,-1), (62,1), (33,-1), (58,1), (29,-1), (54,1), (36,-1)], 4⟩,
    ⟨13, 18, 21, 29, [(36,-1), (54,1), (61,1), (32,-1), (57,1), (64,3), (35,-1), (53,1), (60,1), (31,-1), (38,-1), (56,1), (27,-3), (34,-1), (59,1), (30,-1), (37,-1), (55,1), (91,-3), (62,1), (33,-1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment183_checked : phiCertifiedSegment183.check=true := by decide +kernel

def phiCertifiedSegment184 : PhiCertifiedSegment :=
  ⟨(21/29), (66/91), 5, [
    ⟨21, 29, 66, 91, [(29,-1), (58,1), (36,-1), (54,1), (32,-1), (61,1), (57,1), (35,-1), (64,3), (53,1), (31,-1), (60,1), (38,-1), (27,-3), (56,1), (34,-1), (30,-1), (59,1), (37,-1), (55,1), (33,-1), (62,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment184_checked : phiCertifiedSegment184.check=true := by decide +kernel

def phiCertifiedSegment185 : PhiCertifiedSegment :=
  ⟨(66/91), (27/37), 7, [
    ⟨66, 91, 45, 62, [(91,-3), (29,-1), (58,1), (36,-1), (54,1), (32,-1), (61,1), (57,1), (35,-1), (64,3), (53,1), (31,-1), (60,1), (38,-1), (27,-3), (56,1), (34,-1), (30,-1), (59,1), (37,-1), (55,1), (33,-1), (62,1)], 7⟩,
    ⟨45, 62, 8, 11, [(62,1), (29,-1), (91,-3), (58,1), (36,-1), (54,1), (32,-1), (61,1), (57,1), (35,-1), (64,3), (53,1), (31,-1), (60,1), (38,-1), (27,-3), (56,1), (34,-1), (30,-1), (59,1), (37,-1), (55,1), (33,-1)], 7⟩,
    ⟨8, 11, 43, 59, [(33,-1), (55,1), (29,-1), (62,1), (36,-1), (58,1), (91,-3), (32,-1), (54,1), (61,1), (35,-1), (57,1), (31,-1), (53,1), (64,3), (27,-3), (38,-1), (60,1), (34,-1), (56,1), (30,-1), (37,-1), (59,1)], 7⟩,
    ⟨43, 59, 27, 37, [(59,1), (33,-1), (55,1), (29,-1), (62,1), (36,-1), (58,1), (32,-1), (91,-3), (54,1), (61,1), (35,-1), (57,1), (31,-1), (53,1), (64,3), (27,-3), (38,-1), (60,1), (34,-1), (56,1), (30,-1), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment185_checked : phiCertifiedSegment185.check=true := by decide +kernel

def phiCertifiedSegment186 : PhiCertifiedSegment :=
  ⟨(27/37), (19/26), 6, [
    ⟨27, 37, 19, 26, [(37,-1), (59,1), (33,-1), (55,1), (29,-1), (62,1), (36,-1), (58,1), (32,-1), (54,1), (91,-3), (61,1), (35,-1), (57,1), (31,-1), (53,1), (27,-3), (64,3), (38,-1), (60,1), (34,-1), (56,1), (30,-1)], 6⟩]⟩

lemma phiCertifiedSegment186_checked : phiCertifiedSegment186.check=true := by decide +kernel

def phiCertifiedSegment187 : PhiCertifiedSegment :=
  ⟨(19/26), (67/91), 5, [
    ⟨19, 26, 41, 56, [(37,-1), (33,-1), (59,1), (29,-1), (55,1), (36,-1), (62,1), (32,-1), (58,1), (54,1), (91,-3), (35,-1), (61,1), (31,-1), (57,1), (27,-3), (53,1), (38,-1), (64,3), (34,-1), (60,1), (30,-1), (56,1)], 5⟩,
    ⟨41, 56, 11, 15, [(56,1), (37,-1), (33,-1), (59,1), (29,-1), (55,1), (36,-1), (62,1), (32,-1), (58,1), (54,1), (35,-1), (91,-3), (61,1), (31,-1), (57,1), (27,-3), (53,1), (38,-1), (64,3), (34,-1), (60,1), (30,-1)], 5⟩,
    ⟨11, 15, 47, 64, [(30,-1), (60,1), (56,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (35,-1), (31,-1), (61,1), (91,-3), (27,-3), (57,1), (38,-1), (53,1), (34,-1), (64,3)], 5⟩,
    ⟨47, 64, 25, 34, [(64,3), (30,-1), (60,1), (56,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (35,-1), (31,-1), (61,1), (27,-3), (91,-3), (57,1), (38,-1), (53,1), (34,-1)], 5⟩,
    ⟨25, 34, 39, 53, [(34,-1), (30,-1), (64,3), (60,1), (56,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (91,-3), (38,-1), (53,1)], 5⟩,
    ⟨39, 53, 67, 91, [(53,1), (34,-1), (30,-1), (64,3), (60,1), (56,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (38,-1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment187_checked : phiCertifiedSegment187.check=true := by decide +kernel

def phiCertifiedSegment188 : PhiCertifiedSegment :=
  ⟨(67/91), (14/19), 7, [
    ⟨67, 91, 14, 19, [(91,-3), (53,1), (34,-1), (30,-1), (64,3), (60,1), (56,1), (37,-1), (33,-1), (29,-1), (59,1), (55,1), (36,-1), (32,-1), (62,1), (58,1), (54,1), (35,-1), (31,-1), (27,-3), (61,1), (57,1), (38,-1)], 7⟩]⟩

lemma phiCertifiedSegment188_checked : phiCertifiedSegment188.check=true := by decide +kernel

def phiCertifiedSegment189 : PhiCertifiedSegment :=
  ⟨(14/19), (17/23), 8, [
    ⟨14, 19, 45, 61, [(38,-1), (57,1), (34,-1), (53,1), (91,-3), (30,-1), (64,3), (60,1), (37,-1), (56,1), (33,-1), (29,-1), (59,1), (36,-1), (55,1), (32,-1), (62,1), (58,1), (35,-1), (54,1), (31,-1), (27,-3), (61,1)], 8⟩,
    ⟨45, 61, 17, 23, [(61,1), (38,-1), (57,1), (34,-1), (53,1), (30,-1), (91,-3), (64,3), (60,1), (37,-1), (56,1), (33,-1), (29,-1), (59,1), (36,-1), (55,1), (32,-1), (62,1), (58,1), (35,-1), (54,1), (31,-1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment189_checked : phiCertifiedSegment189.check=true := by decide +kernel

def phiCertifiedSegment190 : PhiCertifiedSegment :=
  ⟨(17/23), (20/27), 9, [
    ⟨17, 23, 20, 27, [(38,-1), (61,1), (34,-1), (57,1), (30,-1), (53,1), (91,-3), (64,3), (37,-1), (60,1), (33,-1), (56,1), (29,-1), (36,-1), (59,1), (32,-1), (55,1), (62,1), (35,-1), (58,1), (31,-1), (54,1), (27,-3)], 9⟩]⟩

lemma phiCertifiedSegment190_checked : phiCertifiedSegment190.check=true := by decide +kernel

def phiCertifiedSegment191 : PhiCertifiedSegment :=
  ⟨(20/27), (23/31), 4, [
    ⟨20, 27, 43, 58, [(27,-3), (54,1), (38,-1), (34,-1), (61,1), (30,-1), (57,1), (53,1), (37,-1), (64,3), (91,-3), (33,-1), (60,1), (29,-1), (56,1), (36,-1), (32,-1), (59,1), (55,1), (35,-1), (62,1), (31,-1), (58,1)], 4⟩,
    ⟨43, 58, 23, 31, [(58,1), (27,-3), (54,1), (38,-1), (34,-1), (61,1), (30,-1), (57,1), (53,1), (37,-1), (64,3), (33,-1), (91,-3), (60,1), (29,-1), (56,1), (36,-1), (32,-1), (59,1), (55,1), (35,-1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment191_checked : phiCertifiedSegment191.check=true := by decide +kernel

def phiCertifiedSegment192 : PhiCertifiedSegment :=
  ⟨(23/31), (3/4), 5, [
    ⟨23, 31, 26, 35, [(31,-1), (62,1), (27,-3), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (64,3), (29,-1), (60,1), (91,-3), (56,1), (36,-1), (32,-1), (59,1), (55,1), (35,-1)], 5⟩,
    ⟨26, 35, 41, 55, [(35,-1), (31,-1), (27,-3), (62,1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (29,-1), (64,3), (60,1), (56,1), (91,-3), (36,-1), (32,-1), (59,1), (55,1)], 5⟩,
    ⟨41, 55, 44, 59, [(55,1), (35,-1), (31,-1), (27,-3), (62,1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (29,-1), (64,3), (60,1), (56,1), (36,-1), (91,-3), (32,-1), (59,1)], 5⟩,
    ⟨44, 59, 68, 91, [(59,1), (55,1), (35,-1), (31,-1), (27,-3), (62,1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (29,-1), (64,3), (60,1), (56,1), (36,-1), (32,-1), (91,-3)], 5⟩,
    ⟨68, 91, 3, 4, [(91,-3), (59,1), (55,1), (35,-1), (31,-1), (27,-3), (62,1), (58,1), (54,1), (38,-1), (34,-1), (30,-1), (61,1), (57,1), (53,1), (37,-1), (33,-1), (29,-1), (64,3), (60,1), (56,1), (36,-1), (32,-1)], 5⟩]⟩

lemma phiCertifiedSegment192_checked : phiCertifiedSegment192.check=true := by decide +kernel

def phiCertifiedSegment193 : PhiCertifiedSegment :=
  ⟨(3/4), (28/37), 2, [
    ⟨3, 4, 46, 61, [(32,-1), (36,-1), (56,1), (60,1), (64,3), (27,-3), (31,-1), (35,-1), (55,1), (59,1), (91,-3), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (62,1), (29,-1), (33,-1), (37,-1), (53,1), (57,1), (61,1)], 2⟩,
    ⟨46, 61, 43, 57, [(61,1), (32,-1), (36,-1), (56,1), (60,1), (64,3), (27,-3), (31,-1), (35,-1), (55,1), (59,1), (30,-1), (91,-3), (34,-1), (38,-1), (54,1), (58,1), (62,1), (29,-1), (33,-1), (37,-1), (53,1), (57,1)], 2⟩,
    ⟨43, 57, 40, 53, [(57,1), (61,1), (32,-1), (36,-1), (56,1), (60,1), (64,3), (27,-3), (31,-1), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (91,-3), (38,-1), (54,1), (58,1), (62,1), (29,-1), (33,-1), (37,-1), (53,1)], 2⟩,
    ⟨40, 53, 28, 37, [(53,1), (57,1), (61,1), (32,-1), (36,-1), (56,1), (60,1), (64,3), (27,-3), (31,-1), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (38,-1), (91,-3), (54,1), (58,1), (62,1), (29,-1), (33,-1), (37,-1)], 2⟩]⟩

lemma phiCertifiedSegment193_checked : phiCertifiedSegment193.check=true := by decide +kernel

def phiCertifiedSegment194 : PhiCertifiedSegment :=
  ⟨(28/37), (25/33), 3, [
    ⟨28, 37, 25, 33, [(37,-1), (53,1), (57,1), (61,1), (32,-1), (36,-1), (56,1), (60,1), (27,-3), (64,3), (31,-1), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (38,-1), (54,1), (91,-3), (58,1), (62,1), (29,-1), (33,-1)], 3⟩]⟩

lemma phiCertifiedSegment194_checked : phiCertifiedSegment194.check=true := by decide +kernel

def phiCertifiedSegment195 : PhiCertifiedSegment :=
  ⟨(25/33), (69/91), 4, [
    ⟨25, 33, 47, 62, [(33,-1), (37,-1), (53,1), (57,1), (61,1), (32,-1), (36,-1), (56,1), (27,-3), (60,1), (31,-1), (64,3), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (91,-3), (29,-1), (62,1)], 4⟩,
    ⟨47, 62, 69, 91, [(62,1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (32,-1), (36,-1), (56,1), (27,-3), (60,1), (31,-1), (64,3), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (29,-1), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment195_checked : phiCertifiedSegment195.check=true := by decide +kernel

def phiCertifiedSegment196 : PhiCertifiedSegment :=
  ⟨(69/91), (13/17), 5, [
    ⟨69, 91, 22, 29, [(91,-3), (62,1), (33,-1), (37,-1), (53,1), (57,1), (61,1), (32,-1), (36,-1), (56,1), (27,-3), (60,1), (31,-1), (64,3), (35,-1), (55,1), (59,1), (30,-1), (34,-1), (38,-1), (54,1), (58,1), (29,-1)], 5⟩,
    ⟨22, 29, 41, 54, [(29,-1), (58,1), (33,-1), (62,1), (91,-3), (37,-1), (53,1), (57,1), (32,-1), (61,1), (36,-1), (27,-3), (56,1), (31,-1), (60,1), (35,-1), (64,3), (55,1), (30,-1), (59,1), (34,-1), (38,-1), (54,1)], 5⟩,
    ⟨41, 54, 19, 25, [(54,1), (29,-1), (58,1), (33,-1), (62,1), (37,-1), (91,-3), (53,1), (57,1), (32,-1), (61,1), (36,-1), (27,-3), (56,1), (31,-1), (60,1), (35,-1), (64,3), (55,1), (30,-1), (59,1), (34,-1), (38,-1)], 5⟩,
    ⟨19, 25, 16, 21, [(29,-1), (54,1), (33,-1), (58,1), (37,-1), (62,1), (91,-3), (53,1), (32,-1), (57,1), (36,-1), (61,1), (27,-3), (31,-1), (56,1), (35,-1), (60,1), (64,3), (30,-1), (55,1), (34,-1), (59,1), (38,-1)], 5⟩,
    ⟨16, 21, 45, 59, [(29,-1), (33,-1), (54,1), (37,-1), (58,1), (62,1), (91,-3), (32,-1), (53,1), (36,-1), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1), (55,1), (38,-1), (59,1)], 5⟩,
    ⟨45, 59, 29, 38, [(59,1), (29,-1), (33,-1), (54,1), (37,-1), (58,1), (62,1), (32,-1), (91,-3), (53,1), (36,-1), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1), (55,1), (38,-1)], 5⟩,
    ⟨29, 38, 42, 55, [(38,-1), (59,1), (29,-1), (33,-1), (54,1), (37,-1), (58,1), (62,1), (32,-1), (53,1), (91,-3), (36,-1), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1), (55,1)], 5⟩,
    ⟨42, 55, 13, 17, [(55,1), (38,-1), (59,1), (29,-1), (33,-1), (54,1), (37,-1), (58,1), (62,1), (32,-1), (53,1), (36,-1), (91,-3), (57,1), (61,1), (27,-3), (31,-1), (35,-1), (56,1), (60,1), (64,3), (30,-1), (34,-1)], 5⟩]⟩

lemma phiCertifiedSegment196_checked : phiCertifiedSegment196.check=true := by decide +kernel

def phiCertifiedSegment197 : PhiCertifiedSegment :=
  ⟨(13/17), (10/13), 6, [
    ⟨13, 17, 49, 64, [(34,-1), (38,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (53,1), (57,1), (91,-3), (27,-3), (61,1), (31,-1), (35,-1), (56,1), (60,1), (30,-1), (64,3)], 6⟩,
    ⟨49, 64, 23, 30, [(64,3), (34,-1), (38,-1), (55,1), (59,1), (29,-1), (33,-1), (37,-1), (54,1), (58,1), (62,1), (32,-1), (36,-1), (53,1), (57,1), (27,-3), (91,-3), (61,1), (31,-1), (35,-1), (56,1), (60,1), (30,-1)], 6⟩,
    ⟨23, 30, 43, 56, [(30,-1), (60,1), (34,-1), (64,3), (38,-1), (55,1), (29,-1), (59,1), (33,-1), (37,-1), (54,1), (58,1), (32,-1), (62,1), (36,-1), (53,1), (27,-3), (57,1), (31,-1), (61,1), (91,-3), (35,-1), (56,1)], 6⟩,
    ⟨43, 56, 10, 13, [(56,1), (30,-1), (60,1), (34,-1), (64,3), (38,-1), (55,1), (29,-1), (59,1), (33,-1), (37,-1), (54,1), (58,1), (32,-1), (62,1), (36,-1), (53,1), (27,-3), (57,1), (31,-1), (61,1), (35,-1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment197_checked : phiCertifiedSegment197.check=true := by decide +kernel

def phiCertifiedSegment198 : PhiCertifiedSegment :=
  ⟨(10/13), (27/35), 8, [
    ⟨10, 13, 47, 61, [(91,-3), (30,-1), (56,1), (34,-1), (60,1), (38,-1), (64,3), (29,-1), (55,1), (33,-1), (59,1), (37,-1), (54,1), (32,-1), (58,1), (36,-1), (62,1), (27,-3), (53,1), (31,-1), (57,1), (35,-1), (61,1)], 8⟩,
    ⟨47, 61, 27, 35, [(61,1), (30,-1), (91,-3), (56,1), (34,-1), (60,1), (38,-1), (64,3), (29,-1), (55,1), (33,-1), (59,1), (37,-1), (54,1), (32,-1), (58,1), (36,-1), (62,1), (27,-3), (53,1), (31,-1), (57,1), (35,-1)], 8⟩]⟩

lemma phiCertifiedSegment198_checked : phiCertifiedSegment198.check=true := by decide +kernel

def phiCertifiedSegment199 : PhiCertifiedSegment :=
  ⟨(27/35), (7/9), 7, [
    ⟨27, 35, 44, 57, [(35,-1), (61,1), (30,-1), (56,1), (91,-3), (34,-1), (60,1), (38,-1), (29,-1), (64,3), (55,1), (33,-1), (59,1), (37,-1), (54,1), (32,-1), (58,1), (36,-1), (27,-3), (62,1), (53,1), (31,-1), (57,1)], 7⟩,
    ⟨44, 57, 17, 22, [(57,1), (35,-1), (61,1), (30,-1), (56,1), (34,-1), (91,-3), (60,1), (38,-1), (29,-1), (64,3), (55,1), (33,-1), (59,1), (37,-1), (54,1), (32,-1), (58,1), (36,-1), (27,-3), (62,1), (53,1), (31,-1)], 7⟩,
    ⟨17, 22, 41, 53, [(35,-1), (57,1), (61,1), (30,-1), (34,-1), (56,1), (91,-3), (38,-1), (60,1), (29,-1), (64,3), (33,-1), (55,1), (37,-1), (59,1), (32,-1), (54,1), (36,-1), (58,1), (27,-3), (62,1), (31,-1), (53,1)], 7⟩,
    ⟨41, 53, 24, 31, [(53,1), (35,-1), (57,1), (61,1), (30,-1), (34,-1), (56,1), (38,-1), (91,-3), (60,1), (29,-1), (64,3), (33,-1), (55,1), (37,-1), (59,1), (32,-1), (54,1), (36,-1), (58,1), (27,-3), (62,1), (31,-1)], 7⟩,
    ⟨24, 31, 45, 58, [(31,-1), (62,1), (53,1), (35,-1), (57,1), (30,-1), (61,1), (34,-1), (56,1), (38,-1), (29,-1), (60,1), (91,-3), (33,-1), (64,3), (55,1), (37,-1), (59,1), (32,-1), (54,1), (36,-1), (27,-3), (58,1)], 7⟩,
    ⟨45, 58, 7, 9, [(58,1), (31,-1), (62,1), (53,1), (35,-1), (57,1), (30,-1), (61,1), (34,-1), (56,1), (38,-1), (29,-1), (60,1), (33,-1), (91,-3), (64,3), (55,1), (37,-1), (59,1), (32,-1), (54,1), (36,-1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment199_checked : phiCertifiedSegment199.check=true := by decide +kernel

def phiCertifiedSegment200 : PhiCertifiedSegment :=
  ⟨(7/9), (11/14), 4, [
    ⟨7, 9, 46, 59, [(27,-3), (36,-1), (54,1), (31,-1), (58,1), (35,-1), (53,1), (62,1), (30,-1), (57,1), (34,-1), (61,1), (29,-1), (38,-1), (56,1), (33,-1), (60,1), (37,-1), (55,1), (64,3), (91,-3), (32,-1), (59,1)], 4⟩,
    ⟨46, 59, 71, 91, [(59,1), (27,-3), (36,-1), (54,1), (31,-1), (58,1), (35,-1), (53,1), (62,1), (30,-1), (57,1), (34,-1), (61,1), (29,-1), (38,-1), (56,1), (33,-1), (60,1), (37,-1), (55,1), (64,3), (32,-1), (91,-3)], 4⟩,
    ⟨71, 91, 25, 32, [(91,-3), (59,1), (27,-3), (36,-1), (54,1), (31,-1), (58,1), (35,-1), (53,1), (62,1), (30,-1), (57,1), (34,-1), (61,1), (29,-1), (38,-1), (56,1), (33,-1), (60,1), (37,-1), (55,1), (64,3), (32,-1)], 4⟩,
    ⟨25, 32, 43, 55, [(32,-1), (64,3), (27,-3), (59,1), (91,-3), (36,-1), (54,1), (31,-1), (58,1), (35,-1), (53,1), (30,-1), (62,1), (57,1), (34,-1), (29,-1), (61,1), (38,-1), (56,1), (33,-1), (60,1), (37,-1), (55,1)], 4⟩,
    ⟨43, 55, 18, 23, [(55,1), (32,-1), (64,3), (27,-3), (59,1), (36,-1), (91,-3), (54,1), (31,-1), (58,1), (35,-1), (53,1), (30,-1), (62,1), (57,1), (34,-1), (29,-1), (61,1), (38,-1), (56,1), (33,-1), (60,1), (37,-1)], 4⟩,
    ⟨18, 23, 47, 60, [(32,-1), (55,1), (64,3), (27,-3), (36,-1), (59,1), (91,-3), (31,-1), (54,1), (35,-1), (58,1), (30,-1), (53,1), (62,1), (34,-1), (57,1), (29,-1), (38,-1), (61,1), (33,-1), (56,1), (37,-1), (60,1)], 4⟩,
    ⟨47, 60, 29, 37, [(60,1), (32,-1), (55,1), (64,3), (27,-3), (36,-1), (59,1), (31,-1), (91,-3), (54,1), (35,-1), (58,1), (30,-1), (53,1), (62,1), (34,-1), (57,1), (29,-1), (38,-1), (61,1), (33,-1), (56,1), (37,-1)], 4⟩,
    ⟨29, 37, 11, 14, [(37,-1), (60,1), (32,-1), (55,1), (27,-3), (64,3), (36,-1), (59,1), (31,-1), (54,1), (91,-3), (35,-1), (58,1), (30,-1), (53,1), (62,1), (34,-1), (57,1), (29,-1), (38,-1), (61,1), (33,-1), (56,1)], 4⟩]⟩

lemma phiCertifiedSegment200_checked : phiCertifiedSegment200.check=true := by decide +kernel

def phiCertifiedSegment201 : PhiCertifiedSegment :=
  ⟨(11/14), (26/33), 3, [
    ⟨11, 14, 48, 61, [(56,1), (37,-1), (32,-1), (60,1), (27,-3), (55,1), (36,-1), (64,3), (31,-1), (59,1), (54,1), (35,-1), (91,-3), (30,-1), (58,1), (53,1), (34,-1), (62,1), (29,-1), (57,1), (38,-1), (33,-1), (61,1)], 3⟩,
    ⟨48, 61, 26, 33, [(61,1), (56,1), (37,-1), (32,-1), (60,1), (27,-3), (55,1), (36,-1), (64,3), (31,-1), (59,1), (54,1), (35,-1), (30,-1), (91,-3), (58,1), (53,1), (34,-1), (62,1), (29,-1), (57,1), (38,-1), (33,-1)], 3⟩]⟩

lemma phiCertifiedSegment201_checked : phiCertifiedSegment201.check=true := by decide +kernel

def phiCertifiedSegment202 : PhiCertifiedSegment :=
  ⟨(26/33), (15/19), 4, [
    ⟨26, 33, 15, 19, [(33,-1), (61,1), (56,1), (37,-1), (32,-1), (27,-3), (60,1), (55,1), (36,-1), (31,-1), (64,3), (59,1), (54,1), (35,-1), (30,-1), (58,1), (91,-3), (53,1), (34,-1), (29,-1), (62,1), (57,1), (38,-1)], 4⟩]⟩

lemma phiCertifiedSegment202_checked : phiCertifiedSegment202.check=true := by decide +kernel

def phiCertifiedSegment203 : PhiCertifiedSegment :=
  ⟨(15/19), (19/24), 5, [
    ⟨15, 19, 49, 62, [(38,-1), (57,1), (33,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (60,1), (36,-1), (55,1), (31,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (58,1), (34,-1), (53,1), (91,-3), (29,-1), (62,1)], 5⟩,
    ⟨49, 62, 72, 91, [(62,1), (38,-1), (57,1), (33,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (60,1), (36,-1), (55,1), (31,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (58,1), (34,-1), (53,1), (29,-1), (91,-3)], 5⟩,
    ⟨72, 91, 19, 24, [(91,-3), (62,1), (38,-1), (57,1), (33,-1), (61,1), (37,-1), (56,1), (32,-1), (27,-3), (60,1), (36,-1), (55,1), (31,-1), (64,3), (59,1), (35,-1), (54,1), (30,-1), (58,1), (34,-1), (53,1), (29,-1)], 5⟩]⟩

lemma phiCertifiedSegment203_checked : phiCertifiedSegment203.check=true := by decide +kernel

def phiCertifiedSegment204 : PhiCertifiedSegment :=
  ⟨(19/24), (4/5), 4, [
    ⟨19, 24, 42, 53, [(91,-3), (38,-1), (62,1), (33,-1), (57,1), (37,-1), (61,1), (32,-1), (56,1), (27,-3), (36,-1), (60,1), (31,-1), (55,1), (64,3), (35,-1), (59,1), (30,-1), (54,1), (34,-1), (58,1), (29,-1), (53,1)], 4⟩,
    ⟨42, 53, 23, 29, [(53,1), (38,-1), (91,-3), (62,1), (33,-1), (57,1), (37,-1), (61,1), (32,-1), (56,1), (27,-3), (36,-1), (60,1), (31,-1), (55,1), (64,3), (35,-1), (59,1), (30,-1), (54,1), (34,-1), (58,1), (29,-1)], 4⟩,
    ⟨23, 29, 27, 34, [(29,-1), (58,1), (53,1), (38,-1), (33,-1), (62,1), (91,-3), (57,1), (37,-1), (32,-1), (61,1), (27,-3), (56,1), (36,-1), (31,-1), (60,1), (55,1), (35,-1), (64,3), (30,-1), (59,1), (54,1), (34,-1)], 4⟩,
    ⟨27, 34, 43, 54, [(34,-1), (29,-1), (58,1), (53,1), (38,-1), (33,-1), (62,1), (57,1), (91,-3), (37,-1), (32,-1), (27,-3), (61,1), (56,1), (36,-1), (31,-1), (60,1), (55,1), (35,-1), (30,-1), (64,3), (59,1), (54,1)], 4⟩,
    ⟨43, 54, 47, 59, [(54,1), (34,-1), (29,-1), (58,1), (53,1), (38,-1), (33,-1), (62,1), (57,1), (37,-1), (91,-3), (32,-1), (27,-3), (61,1), (56,1), (36,-1), (31,-1), (60,1), (55,1), (35,-1), (30,-1), (64,3), (59,1)], 4⟩,
    ⟨47, 59, 51, 64, [(59,1), (54,1), (34,-1), (29,-1), (58,1), (53,1), (38,-1), (33,-1), (62,1), (57,1), (37,-1), (32,-1), (91,-3), (27,-3), (61,1), (56,1), (36,-1), (31,-1), (60,1), (55,1), (35,-1), (30,-1), (64,3)], 4⟩,
    ⟨51, 64, 4, 5, [(64,3), (59,1), (54,1), (34,-1), (29,-1), (58,1), (53,1), (38,-1), (33,-1), (62,1), (57,1), (37,-1), (32,-1), (27,-3), (91,-3), (61,1), (56,1), (36,-1), (31,-1), (60,1), (55,1), (35,-1), (30,-1)], 4⟩]⟩

lemma phiCertifiedSegment204_checked : phiCertifiedSegment204.check=true := by decide +kernel

def phiCertifiedSegment205 : PhiCertifiedSegment :=
  ⟨(4/5), (73/91), 6, [
    ⟨4, 5, 73, 91, [(30,-1), (35,-1), (55,1), (60,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (31,-1), (36,-1), (56,1), (61,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment205_checked : phiCertifiedSegment205.check=true := by decide +kernel

def phiCertifiedSegment206 : PhiCertifiedSegment :=
  ⟨(73/91), (25/31), 7, [
    ⟨73, 91, 49, 61, [(91,-3), (30,-1), (35,-1), (55,1), (60,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (31,-1), (36,-1), (56,1), (61,1)], 7⟩,
    ⟨49, 61, 45, 56, [(61,1), (30,-1), (91,-3), (35,-1), (55,1), (60,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (31,-1), (36,-1), (56,1)], 7⟩,
    ⟨45, 56, 29, 36, [(56,1), (61,1), (30,-1), (35,-1), (91,-3), (55,1), (60,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (31,-1), (36,-1)], 7⟩,
    ⟨29, 36, 25, 31, [(36,-1), (56,1), (61,1), (30,-1), (35,-1), (55,1), (91,-3), (60,1), (29,-1), (34,-1), (54,1), (59,1), (64,3), (33,-1), (38,-1), (53,1), (58,1), (27,-3), (32,-1), (37,-1), (57,1), (62,1), (31,-1)], 7⟩]⟩

lemma phiCertifiedSegment206_checked : phiCertifiedSegment206.check=true := by decide +kernel

def phiCertifiedSegment207 : PhiCertifiedSegment :=
  ⟨(25/31), (30/37), 8, [
    ⟨25, 31, 46, 57, [(31,-1), (62,1), (36,-1), (56,1), (30,-1), (61,1), (35,-1), (55,1), (29,-1), (60,1), (91,-3), (34,-1), (54,1), (59,1), (33,-1), (64,3), (38,-1), (53,1), (27,-3), (58,1), (32,-1), (37,-1), (57,1)], 8⟩,
    ⟨46, 57, 21, 26, [(57,1), (31,-1), (62,1), (36,-1), (56,1), (30,-1), (61,1), (35,-1), (55,1), (29,-1), (60,1), (34,-1), (91,-3), (54,1), (59,1), (33,-1), (64,3), (38,-1), (53,1), (27,-3), (58,1), (32,-1), (37,-1)], 8⟩,
    ⟨21, 26, 17, 21, [(31,-1), (57,1), (36,-1), (62,1), (30,-1), (56,1), (35,-1), (61,1), (29,-1), (55,1), (34,-1), (60,1), (91,-3), (54,1), (33,-1), (59,1), (38,-1), (64,3), (27,-3), (53,1), (32,-1), (58,1), (37,-1)], 8⟩,
    ⟨17, 21, 47, 58, [(31,-1), (36,-1), (57,1), (62,1), (30,-1), (35,-1), (56,1), (61,1), (29,-1), (34,-1), (55,1), (60,1), (91,-3), (33,-1), (54,1), (38,-1), (59,1), (64,3), (27,-3), (32,-1), (53,1), (37,-1), (58,1)], 8⟩,
    ⟨47, 58, 30, 37, [(58,1), (31,-1), (36,-1), (57,1), (62,1), (30,-1), (35,-1), (56,1), (61,1), (29,-1), (34,-1), (55,1), (60,1), (33,-1), (91,-3), (54,1), (38,-1), (59,1), (64,3), (27,-3), (32,-1), (53,1), (37,-1)], 8⟩]⟩

lemma phiCertifiedSegment207_checked : phiCertifiedSegment207.check=true := by decide +kernel

def phiCertifiedSegment208 : PhiCertifiedSegment :=
  ⟨(30/37), (74/91), 6, [
    ⟨30, 37, 43, 53, [(37,-1), (58,1), (31,-1), (36,-1), (57,1), (62,1), (30,-1), (35,-1), (56,1), (61,1), (29,-1), (34,-1), (55,1), (60,1), (33,-1), (54,1), (91,-3), (38,-1), (59,1), (27,-3), (64,3), (32,-1), (53,1)], 6⟩,
    ⟨43, 53, 13, 16, [(53,1), (37,-1), (58,1), (31,-1), (36,-1), (57,1), (62,1), (30,-1), (35,-1), (56,1), (61,1), (29,-1), (34,-1), (55,1), (60,1), (33,-1), (54,1), (38,-1), (91,-3), (59,1), (27,-3), (64,3), (32,-1)], 6⟩,
    ⟨13, 16, 74, 91, [(32,-1), (64,3), (37,-1), (53,1), (58,1), (31,-1), (36,-1), (57,1), (30,-1), (62,1), (35,-1), (56,1), (29,-1), (61,1), (34,-1), (55,1), (60,1), (33,-1), (38,-1), (54,1), (27,-3), (59,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment208_checked : phiCertifiedSegment208.check=true := by decide +kernel

def phiCertifiedSegment209 : PhiCertifiedSegment :=
  ⟨(74/91), (22/27), 8, [
    ⟨74, 91, 48, 59, [(91,-3), (32,-1), (64,3), (37,-1), (53,1), (58,1), (31,-1), (36,-1), (57,1), (30,-1), (62,1), (35,-1), (56,1), (29,-1), (61,1), (34,-1), (55,1), (60,1), (33,-1), (38,-1), (54,1), (27,-3), (59,1)], 8⟩,
    ⟨48, 59, 22, 27, [(59,1), (32,-1), (91,-3), (64,3), (37,-1), (53,1), (58,1), (31,-1), (36,-1), (57,1), (30,-1), (62,1), (35,-1), (56,1), (29,-1), (61,1), (34,-1), (55,1), (60,1), (33,-1), (38,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment209_checked : phiCertifiedSegment209.check=true := by decide +kernel

def phiCertifiedSegment210 : PhiCertifiedSegment :=
  ⟨(22/27), (23/28), 4, [
    ⟨22, 27, 31, 38, [(27,-3), (54,1), (32,-1), (59,1), (37,-1), (64,3), (91,-3), (53,1), (31,-1), (58,1), (36,-1), (30,-1), (57,1), (35,-1), (62,1), (29,-1), (56,1), (34,-1), (61,1), (55,1), (33,-1), (60,1), (38,-1)], 4⟩,
    ⟨31, 38, 49, 60, [(38,-1), (27,-3), (54,1), (32,-1), (59,1), (37,-1), (64,3), (53,1), (91,-3), (31,-1), (58,1), (36,-1), (30,-1), (57,1), (35,-1), (62,1), (29,-1), (56,1), (34,-1), (61,1), (55,1), (33,-1), (60,1)], 4⟩,
    ⟨49, 60, 9, 11, [(60,1), (38,-1), (27,-3), (54,1), (32,-1), (59,1), (37,-1), (64,3), (53,1), (31,-1), (91,-3), (58,1), (36,-1), (30,-1), (57,1), (35,-1), (62,1), (29,-1), (56,1), (34,-1), (61,1), (55,1), (33,-1)], 4⟩,
    ⟨9, 11, 50, 61, [(33,-1), (55,1), (27,-3), (38,-1), (60,1), (32,-1), (54,1), (37,-1), (59,1), (31,-1), (53,1), (64,3), (36,-1), (58,1), (91,-3), (30,-1), (35,-1), (57,1), (29,-1), (62,1), (34,-1), (56,1), (61,1)], 4⟩,
    ⟨50, 61, 23, 28, [(61,1), (33,-1), (55,1), (27,-3), (38,-1), (60,1), (32,-1), (54,1), (37,-1), (59,1), (31,-1), (53,1), (64,3), (36,-1), (58,1), (30,-1), (91,-3), (35,-1), (57,1), (29,-1), (62,1), (34,-1), (56,1)], 4⟩]⟩

lemma phiCertifiedSegment210_checked : phiCertifiedSegment210.check=true := by decide +kernel

def phiCertifiedSegment211 : PhiCertifiedSegment :=
  ⟨(23/28), (14/17), 3, [
    ⟨23, 28, 51, 62, [(56,1), (33,-1), (61,1), (27,-3), (55,1), (38,-1), (32,-1), (60,1), (54,1), (37,-1), (31,-1), (59,1), (53,1), (36,-1), (64,3), (30,-1), (58,1), (35,-1), (91,-3), (29,-1), (57,1), (34,-1), (62,1)], 3⟩,
    ⟨51, 62, 14, 17, [(62,1), (56,1), (33,-1), (61,1), (27,-3), (55,1), (38,-1), (32,-1), (60,1), (54,1), (37,-1), (31,-1), (59,1), (53,1), (36,-1), (64,3), (30,-1), (58,1), (35,-1), (29,-1), (91,-3), (57,1), (34,-1)], 3⟩]⟩

lemma phiCertifiedSegment211_checked : phiCertifiedSegment211.check=true := by decide +kernel

def phiCertifiedSegment212 : PhiCertifiedSegment :=
  ⟨(14/17), (76/91), 5, [
    ⟨14, 17, 75, 91, [(34,-1), (62,1), (56,1), (33,-1), (27,-3), (61,1), (38,-1), (55,1), (32,-1), (60,1), (37,-1), (54,1), (31,-1), (59,1), (36,-1), (53,1), (30,-1), (64,3), (58,1), (35,-1), (29,-1), (57,1), (91,-3)], 5⟩,
    ⟨75, 91, 47, 57, [(91,-3), (34,-1), (62,1), (56,1), (33,-1), (27,-3), (61,1), (38,-1), (55,1), (32,-1), (60,1), (37,-1), (54,1), (31,-1), (59,1), (36,-1), (53,1), (30,-1), (64,3), (58,1), (35,-1), (29,-1), (57,1)], 5⟩,
    ⟨47, 57, 19, 23, [(57,1), (34,-1), (91,-3), (62,1), (56,1), (33,-1), (27,-3), (61,1), (38,-1), (55,1), (32,-1), (60,1), (37,-1), (54,1), (31,-1), (59,1), (36,-1), (53,1), (30,-1), (64,3), (58,1), (35,-1), (29,-1)], 5⟩,
    ⟨19, 23, 24, 29, [(34,-1), (57,1), (91,-3), (62,1), (33,-1), (56,1), (27,-3), (38,-1), (61,1), (32,-1), (55,1), (37,-1), (60,1), (31,-1), (54,1), (36,-1), (59,1), (30,-1), (53,1), (64,3), (35,-1), (58,1), (29,-1)], 5⟩,
    ⟨24, 29, 53, 64, [(29,-1), (58,1), (34,-1), (57,1), (33,-1), (62,1), (91,-3), (27,-3), (56,1), (38,-1), (32,-1), (61,1), (55,1), (37,-1), (31,-1), (60,1), (54,1), (36,-1), (30,-1), (59,1), (53,1), (35,-1), (64,3)], 5⟩,
    ⟨53, 64, 29, 35, [(64,3), (29,-1), (58,1), (34,-1), (57,1), (33,-1), (62,1), (27,-3), (91,-3), (56,1), (38,-1), (32,-1), (61,1), (55,1), (37,-1), (31,-1), (60,1), (54,1), (36,-1), (30,-1), (59,1), (53,1), (35,-1)], 5⟩,
    ⟨29, 35, 44, 53, [(35,-1), (29,-1), (64,3), (58,1), (34,-1), (57,1), (33,-1), (27,-3), (62,1), (56,1), (91,-3), (38,-1), (32,-1), (61,1), (55,1), (37,-1), (31,-1), (60,1), (54,1), (36,-1), (30,-1), (59,1), (53,1)], 5⟩,
    ⟨44, 53, 49, 59, [(53,1), (35,-1), (29,-1), (64,3), (58,1), (34,-1), (57,1), (33,-1), (27,-3), (62,1), (56,1), (38,-1), (91,-3), (32,-1), (61,1), (55,1), (37,-1), (31,-1), (60,1), (54,1), (36,-1), (30,-1), (59,1)], 5⟩,
    ⟨49, 59, 5, 6, [(59,1), (53,1), (35,-1), (29,-1), (64,3), (58,1), (34,-1), (57,1), (33,-1), (27,-3), (62,1), (56,1), (38,-1), (32,-1), (91,-3), (61,1), (55,1), (37,-1), (31,-1), (60,1), (54,1), (36,-1), (30,-1)], 5⟩,
    ⟨5, 6, 76, 91, [(30,-1), (36,-1), (54,1), (60,1), (29,-1), (35,-1), (53,1), (59,1), (34,-1), (58,1), (64,3), (27,-3), (33,-1), (57,1), (32,-1), (38,-1), (56,1), (62,1), (31,-1), (37,-1), (55,1), (61,1), (91,-3)], 5⟩]⟩

lemma phiCertifiedSegment212_checked : phiCertifiedSegment212.check=true := by decide +kernel

def phiCertifiedSegment213 : PhiCertifiedSegment :=
  ⟨(76/91), (31/37), 6, [
    ⟨76, 91, 51, 61, [(91,-3), (30,-1), (36,-1), (54,1), (60,1), (29,-1), (35,-1), (53,1), (59,1), (34,-1), (58,1), (64,3), (27,-3), (33,-1), (57,1), (32,-1), (38,-1), (56,1), (62,1), (31,-1), (37,-1), (55,1), (61,1)], 6⟩,
    ⟨51, 61, 46, 55, [(61,1), (30,-1), (91,-3), (36,-1), (54,1), (60,1), (29,-1), (35,-1), (53,1), (59,1), (34,-1), (58,1), (64,3), (27,-3), (33,-1), (57,1), (32,-1), (38,-1), (56,1), (62,1), (31,-1), (37,-1), (55,1)], 6⟩,
    ⟨46, 55, 31, 37, [(55,1), (61,1), (30,-1), (36,-1), (91,-3), (54,1), (60,1), (29,-1), (35,-1), (53,1), (59,1), (34,-1), (58,1), (64,3), (27,-3), (33,-1), (57,1), (32,-1), (38,-1), (56,1), (62,1), (31,-1), (37,-1)], 6⟩]⟩

lemma phiCertifiedSegment213_checked : phiCertifiedSegment213.check=true := by decide +kernel

def phiCertifiedSegment214 : PhiCertifiedSegment :=
  ⟨(31/37), (16/19), 5, [
    ⟨31, 37, 26, 31, [(37,-1), (55,1), (61,1), (30,-1), (36,-1), (54,1), (91,-3), (60,1), (29,-1), (35,-1), (53,1), (59,1), (34,-1), (58,1), (27,-3), (64,3), (33,-1), (57,1), (32,-1), (38,-1), (56,1), (62,1), (31,-1)], 5⟩,
    ⟨26, 31, 47, 56, [(31,-1), (62,1), (37,-1), (55,1), (30,-1), (61,1), (36,-1), (54,1), (29,-1), (60,1), (91,-3), (35,-1), (53,1), (59,1), (34,-1), (27,-3), (58,1), (33,-1), (64,3), (57,1), (32,-1), (38,-1), (56,1)], 5⟩,
    ⟨47, 56, 21, 25, [(56,1), (31,-1), (62,1), (37,-1), (55,1), (30,-1), (61,1), (36,-1), (54,1), (29,-1), (60,1), (35,-1), (91,-3), (53,1), (59,1), (34,-1), (27,-3), (58,1), (33,-1), (64,3), (57,1), (32,-1), (38,-1)], 5⟩,
    ⟨21, 25, 16, 19, [(31,-1), (56,1), (37,-1), (62,1), (30,-1), (55,1), (36,-1), (61,1), (29,-1), (54,1), (35,-1), (60,1), (91,-3), (53,1), (34,-1), (59,1), (27,-3), (33,-1), (58,1), (64,3), (32,-1), (57,1), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment214_checked : phiCertifiedSegment214.check=true := by decide +kernel

def phiCertifiedSegment215 : PhiCertifiedSegment :=
  ⟨(16/19), (11/13), 6, [
    ⟨16, 19, 27, 32, [(38,-1), (57,1), (31,-1), (37,-1), (56,1), (62,1), (30,-1), (36,-1), (55,1), (61,1), (29,-1), (35,-1), (54,1), (60,1), (34,-1), (53,1), (91,-3), (59,1), (27,-3), (33,-1), (58,1), (64,3), (32,-1)], 6⟩,
    ⟨27, 32, 49, 58, [(32,-1), (64,3), (38,-1), (57,1), (31,-1), (37,-1), (56,1), (30,-1), (62,1), (36,-1), (55,1), (29,-1), (61,1), (35,-1), (54,1), (60,1), (34,-1), (53,1), (27,-3), (59,1), (91,-3), (33,-1), (58,1)], 6⟩,
    ⟨49, 58, 11, 13, [(58,1), (32,-1), (64,3), (38,-1), (57,1), (31,-1), (37,-1), (56,1), (30,-1), (62,1), (36,-1), (55,1), (29,-1), (61,1), (35,-1), (54,1), (60,1), (34,-1), (53,1), (27,-3), (59,1), (33,-1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment215_checked : phiCertifiedSegment215.check=true := by decide +kernel

def phiCertifiedSegment216 : PhiCertifiedSegment :=
  ⟨(11/13), (23/27), 8, [
    ⟨11, 13, 50, 59, [(91,-3), (32,-1), (58,1), (38,-1), (64,3), (31,-1), (57,1), (37,-1), (30,-1), (56,1), (36,-1), (62,1), (29,-1), (55,1), (35,-1), (61,1), (54,1), (34,-1), (60,1), (27,-3), (53,1), (33,-1), (59,1)], 8⟩,
    ⟨50, 59, 28, 33, [(59,1), (32,-1), (91,-3), (58,1), (38,-1), (64,3), (31,-1), (57,1), (37,-1), (30,-1), (56,1), (36,-1), (62,1), (29,-1), (55,1), (35,-1), (61,1), (54,1), (34,-1), (60,1), (27,-3), (53,1), (33,-1)], 8⟩,
    ⟨28, 33, 45, 53, [(33,-1), (59,1), (32,-1), (58,1), (91,-3), (38,-1), (31,-1), (64,3), (57,1), (37,-1), (30,-1), (56,1), (36,-1), (29,-1), (62,1), (55,1), (35,-1), (61,1), (54,1), (34,-1), (27,-3), (60,1), (53,1)], 8⟩,
    ⟨45, 53, 17, 20, [(53,1), (33,-1), (59,1), (32,-1), (58,1), (38,-1), (91,-3), (31,-1), (64,3), (57,1), (37,-1), (30,-1), (56,1), (36,-1), (29,-1), (62,1), (55,1), (35,-1), (61,1), (54,1), (34,-1), (27,-3), (60,1)], 8⟩,
    ⟨17, 20, 23, 27, [(60,1), (33,-1), (53,1), (59,1), (32,-1), (38,-1), (58,1), (31,-1), (91,-3), (64,3), (37,-1), (57,1), (30,-1), (36,-1), (56,1), (29,-1), (62,1), (35,-1), (55,1), (61,1), (34,-1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment216_checked : phiCertifiedSegment216.check=true := by decide +kernel

def phiCertifiedSegment217 : PhiCertifiedSegment :=
  ⟨(23/27), (31/36), 3, [
    ⟨23, 27, 52, 61, [(27,-3), (54,1), (33,-1), (60,1), (53,1), (32,-1), (59,1), (38,-1), (31,-1), (58,1), (37,-1), (64,3), (91,-3), (30,-1), (57,1), (36,-1), (29,-1), (56,1), (35,-1), (62,1), (55,1), (34,-1), (61,1)], 3⟩,
    ⟨52, 61, 29, 34, [(61,1), (27,-3), (54,1), (33,-1), (60,1), (53,1), (32,-1), (59,1), (38,-1), (31,-1), (58,1), (37,-1), (64,3), (30,-1), (91,-3), (57,1), (36,-1), (29,-1), (56,1), (35,-1), (62,1), (55,1), (34,-1)], 3⟩,
    ⟨29, 34, 47, 55, [(34,-1), (27,-3), (61,1), (54,1), (33,-1), (60,1), (53,1), (32,-1), (59,1), (38,-1), (31,-1), (58,1), (37,-1), (30,-1), (64,3), (57,1), (91,-3), (36,-1), (29,-1), (56,1), (35,-1), (62,1), (55,1)], 3⟩,
    ⟨47, 55, 53, 62, [(55,1), (34,-1), (27,-3), (61,1), (54,1), (33,-1), (60,1), (53,1), (32,-1), (59,1), (38,-1), (31,-1), (58,1), (37,-1), (30,-1), (64,3), (57,1), (36,-1), (91,-3), (29,-1), (56,1), (35,-1), (62,1)], 3⟩,
    ⟨53, 62, 6, 7, [(62,1), (55,1), (34,-1), (27,-3), (61,1), (54,1), (33,-1), (60,1), (53,1), (32,-1), (59,1), (38,-1), (31,-1), (58,1), (37,-1), (30,-1), (64,3), (57,1), (36,-1), (29,-1), (91,-3), (56,1), (35,-1)], 3⟩,
    ⟨6, 7, 55, 64, [(35,-1), (56,1), (91,-3), (27,-3), (34,-1), (55,1), (62,1), (33,-1), (54,1), (61,1), (32,-1), (53,1), (60,1), (31,-1), (38,-1), (59,1), (30,-1), (37,-1), (58,1), (29,-1), (36,-1), (57,1), (64,3)], 3⟩,
    ⟨55, 64, 49, 57, [(64,3), (35,-1), (56,1), (27,-3), (91,-3), (34,-1), (55,1), (62,1), (33,-1), (54,1), (61,1), (32,-1), (53,1), (60,1), (31,-1), (38,-1), (59,1), (30,-1), (37,-1), (58,1), (29,-1), (36,-1), (57,1)], 3⟩,
    ⟨49, 57, 31, 36, [(57,1), (64,3), (35,-1), (56,1), (27,-3), (34,-1), (91,-3), (55,1), (62,1), (33,-1), (54,1), (61,1), (32,-1), (53,1), (60,1), (31,-1), (38,-1), (59,1), (30,-1), (37,-1), (58,1), (29,-1), (36,-1)], 3⟩]⟩

lemma phiCertifiedSegment217_checked : phiCertifiedSegment217.check=true := by decide +kernel

def phiCertifiedSegment218 : PhiCertifiedSegment :=
  ⟨(31/36), (25/29), 4, [
    ⟨31, 36, 25, 29, [(36,-1), (57,1), (64,3), (35,-1), (56,1), (27,-3), (34,-1), (55,1), (91,-3), (62,1), (33,-1), (54,1), (61,1), (32,-1), (53,1), (60,1), (31,-1), (38,-1), (59,1), (30,-1), (37,-1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment218_checked : phiCertifiedSegment218.check=true := by decide +kernel

def phiCertifiedSegment219 : PhiCertifiedSegment :=
  ⟨(25/29), (19/22), 5, [
    ⟨25, 29, 19, 22, [(29,-1), (58,1), (36,-1), (57,1), (35,-1), (64,3), (27,-3), (56,1), (34,-1), (55,1), (33,-1), (62,1), (91,-3), (54,1), (32,-1), (61,1), (53,1), (31,-1), (60,1), (38,-1), (30,-1), (59,1), (37,-1)], 5⟩]⟩

lemma phiCertifiedSegment219_checked : phiCertifiedSegment219.check=true := by decide +kernel

def phiCertifiedSegment220 : PhiCertifiedSegment :=
  ⟨(19/22), (27/31), 4, [
    ⟨19, 22, 51, 59, [(29,-1), (36,-1), (58,1), (35,-1), (57,1), (64,3), (27,-3), (34,-1), (56,1), (33,-1), (55,1), (62,1), (91,-3), (32,-1), (54,1), (61,1), (31,-1), (53,1), (38,-1), (60,1), (30,-1), (37,-1), (59,1)], 4⟩,
    ⟨51, 59, 32, 37, [(59,1), (29,-1), (36,-1), (58,1), (35,-1), (57,1), (64,3), (27,-3), (34,-1), (56,1), (33,-1), (55,1), (62,1), (32,-1), (91,-3), (54,1), (61,1), (31,-1), (53,1), (38,-1), (60,1), (30,-1), (37,-1)], 4⟩,
    ⟨32, 37, 13, 15, [(37,-1), (59,1), (29,-1), (36,-1), (58,1), (35,-1), (57,1), (27,-3), (64,3), (34,-1), (56,1), (33,-1), (55,1), (62,1), (32,-1), (54,1), (91,-3), (61,1), (31,-1), (53,1), (38,-1), (60,1), (30,-1)], 4⟩,
    ⟨13, 15, 46, 53, [(30,-1), (60,1), (37,-1), (29,-1), (59,1), (36,-1), (58,1), (35,-1), (27,-3), (57,1), (34,-1), (64,3), (56,1), (33,-1), (55,1), (32,-1), (62,1), (54,1), (31,-1), (61,1), (91,-3), (38,-1), (53,1)], 4⟩,
    ⟨46, 53, 79, 91, [(53,1), (30,-1), (60,1), (37,-1), (29,-1), (59,1), (36,-1), (58,1), (35,-1), (27,-3), (57,1), (34,-1), (64,3), (56,1), (33,-1), (55,1), (32,-1), (62,1), (54,1), (31,-1), (61,1), (38,-1), (91,-3)], 4⟩,
    ⟨79, 91, 33, 38, [(91,-3), (53,1), (30,-1), (60,1), (37,-1), (29,-1), (59,1), (36,-1), (58,1), (35,-1), (27,-3), (57,1), (34,-1), (64,3), (56,1), (33,-1), (55,1), (32,-1), (62,1), (54,1), (31,-1), (61,1), (38,-1)], 4⟩,
    ⟨33, 38, 53, 61, [(38,-1), (53,1), (91,-3), (30,-1), (60,1), (37,-1), (29,-1), (59,1), (36,-1), (58,1), (35,-1), (27,-3), (57,1), (34,-1), (64,3), (56,1), (33,-1), (55,1), (32,-1), (62,1), (54,1), (31,-1), (61,1)], 4⟩,
    ⟨53, 61, 20, 23, [(61,1), (38,-1), (53,1), (30,-1), (91,-3), (60,1), (37,-1), (29,-1), (59,1), (36,-1), (58,1), (35,-1), (27,-3), (57,1), (34,-1), (64,3), (56,1), (33,-1), (55,1), (32,-1), (62,1), (54,1), (31,-1)], 4⟩,
    ⟨20, 23, 47, 54, [(38,-1), (61,1), (30,-1), (53,1), (91,-3), (37,-1), (60,1), (29,-1), (36,-1), (59,1), (35,-1), (58,1), (27,-3), (34,-1), (57,1), (64,3), (33,-1), (56,1), (32,-1), (55,1), (62,1), (31,-1), (54,1)], 4⟩,
    ⟨47, 54, 27, 31, [(54,1), (38,-1), (61,1), (30,-1), (53,1), (37,-1), (91,-3), (60,1), (29,-1), (36,-1), (59,1), (35,-1), (58,1), (27,-3), (34,-1), (57,1), (64,3), (33,-1), (56,1), (32,-1), (55,1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment220_checked : phiCertifiedSegment220.check=true := by decide +kernel

def phiCertifiedSegment221 : PhiCertifiedSegment :=
  ⟨(27/31), (7/8), 5, [
    ⟨27, 31, 48, 55, [(31,-1), (62,1), (54,1), (38,-1), (30,-1), (61,1), (53,1), (37,-1), (29,-1), (60,1), (91,-3), (36,-1), (59,1), (35,-1), (27,-3), (58,1), (34,-1), (57,1), (33,-1), (64,3), (56,1), (32,-1), (55,1)], 5⟩,
    ⟨48, 55, 7, 8, [(55,1), (31,-1), (62,1), (54,1), (38,-1), (30,-1), (61,1), (53,1), (37,-1), (29,-1), (60,1), (36,-1), (91,-3), (59,1), (35,-1), (27,-3), (58,1), (34,-1), (57,1), (33,-1), (64,3), (56,1), (32,-1)], 5⟩]⟩

lemma phiCertifiedSegment221_checked : phiCertifiedSegment221.check=true := by decide +kernel

def phiCertifiedSegment222 : PhiCertifiedSegment :=
  ⟨(7/8), (29/33), 4, [
    ⟨7, 8, 50, 57, [(32,-1), (56,1), (64,3), (31,-1), (55,1), (30,-1), (38,-1), (54,1), (62,1), (29,-1), (37,-1), (53,1), (61,1), (36,-1), (60,1), (27,-3), (35,-1), (59,1), (91,-3), (34,-1), (58,1), (33,-1), (57,1)], 4⟩,
    ⟨50, 57, 29, 33, [(57,1), (32,-1), (56,1), (64,3), (31,-1), (55,1), (30,-1), (38,-1), (54,1), (62,1), (29,-1), (37,-1), (53,1), (61,1), (36,-1), (60,1), (27,-3), (35,-1), (59,1), (34,-1), (91,-3), (58,1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment222_checked : phiCertifiedSegment222.check=true := by decide +kernel

def phiCertifiedSegment223 : PhiCertifiedSegment :=
  ⟨(29/33), (80/91), 6, [
    ⟨29, 33, 80, 91, [(33,-1), (57,1), (32,-1), (56,1), (31,-1), (64,3), (55,1), (30,-1), (38,-1), (54,1), (29,-1), (62,1), (37,-1), (53,1), (61,1), (36,-1), (27,-3), (60,1), (35,-1), (59,1), (34,-1), (58,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment223_checked : phiCertifiedSegment223.check=true := by decide +kernel

def phiCertifiedSegment224 : PhiCertifiedSegment :=
  ⟨(80/91), (15/17), 8, [
    ⟨80, 91, 51, 58, [(91,-3), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (64,3), (55,1), (30,-1), (38,-1), (54,1), (29,-1), (62,1), (37,-1), (53,1), (61,1), (36,-1), (27,-3), (60,1), (35,-1), (59,1), (34,-1), (58,1)], 8⟩,
    ⟨51, 58, 22, 25, [(58,1), (33,-1), (91,-3), (57,1), (32,-1), (56,1), (31,-1), (64,3), (55,1), (30,-1), (38,-1), (54,1), (29,-1), (62,1), (37,-1), (53,1), (61,1), (36,-1), (27,-3), (60,1), (35,-1), (59,1), (34,-1)], 8⟩,
    ⟨22, 25, 52, 59, [(33,-1), (58,1), (91,-3), (32,-1), (57,1), (31,-1), (56,1), (64,3), (30,-1), (55,1), (38,-1), (29,-1), (54,1), (37,-1), (62,1), (53,1), (36,-1), (61,1), (27,-3), (35,-1), (60,1), (34,-1), (59,1)], 8⟩,
    ⟨52, 59, 15, 17, [(59,1), (33,-1), (58,1), (32,-1), (91,-3), (57,1), (31,-1), (56,1), (64,3), (30,-1), (55,1), (38,-1), (29,-1), (54,1), (37,-1), (62,1), (53,1), (36,-1), (61,1), (27,-3), (35,-1), (60,1), (34,-1)], 8⟩]⟩

lemma phiCertifiedSegment224_checked : phiCertifiedSegment224.check=true := by decide +kernel

def phiCertifiedSegment225 : PhiCertifiedSegment :=
  ⟨(15/17), (23/26), 9, [
    ⟨15, 17, 53, 60, [(34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (91,-3), (31,-1), (56,1), (30,-1), (64,3), (38,-1), (55,1), (29,-1), (37,-1), (54,1), (62,1), (36,-1), (53,1), (27,-3), (61,1), (35,-1), (60,1)], 9⟩,
    ⟨53, 60, 23, 26, [(60,1), (34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (31,-1), (91,-3), (56,1), (30,-1), (64,3), (38,-1), (55,1), (29,-1), (37,-1), (54,1), (62,1), (36,-1), (53,1), (27,-3), (61,1), (35,-1)], 9⟩]⟩

lemma phiCertifiedSegment225_checked : phiCertifiedSegment225.check=true := by decide +kernel

def phiCertifiedSegment226 : PhiCertifiedSegment :=
  ⟨(23/26), (31/35), 8, [
    ⟨23, 26, 54, 61, [(34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (91,-3), (30,-1), (56,1), (38,-1), (64,3), (29,-1), (55,1), (37,-1), (54,1), (36,-1), (62,1), (27,-3), (53,1), (35,-1), (61,1)], 8⟩,
    ⟨54, 61, 31, 35, [(61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (91,-3), (56,1), (38,-1), (64,3), (29,-1), (55,1), (37,-1), (54,1), (36,-1), (62,1), (27,-3), (53,1), (35,-1)], 8⟩]⟩

lemma phiCertifiedSegment226_checked : phiCertifiedSegment226.check=true := by decide +kernel

def phiCertifiedSegment227 : PhiCertifiedSegment :=
  ⟨(31/35), (8/9), 7, [
    ⟨31, 35, 47, 53, [(35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (91,-3), (38,-1), (29,-1), (64,3), (55,1), (37,-1), (54,1), (36,-1), (27,-3), (62,1), (53,1)], 7⟩,
    ⟨47, 53, 55, 62, [(53,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (38,-1), (91,-3), (29,-1), (64,3), (55,1), (37,-1), (54,1), (36,-1), (27,-3), (62,1)], 7⟩,
    ⟨55, 62, 8, 9, [(62,1), (53,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (38,-1), (29,-1), (91,-3), (64,3), (55,1), (37,-1), (54,1), (36,-1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment227_checked : phiCertifiedSegment227.check=true := by decide +kernel

def phiCertifiedSegment228 : PhiCertifiedSegment :=
  ⟨(8/9), (26/29), 4, [
    ⟨8, 9, 81, 91, [(27,-3), (36,-1), (54,1), (35,-1), (53,1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (38,-1), (56,1), (37,-1), (55,1), (64,3), (91,-3)], 4⟩,
    ⟨81, 91, 57, 64, [(91,-3), (27,-3), (36,-1), (54,1), (35,-1), (53,1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (38,-1), (56,1), (37,-1), (55,1), (64,3)], 4⟩,
    ⟨57, 64, 49, 55, [(64,3), (27,-3), (91,-3), (36,-1), (54,1), (35,-1), (53,1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (38,-1), (56,1), (37,-1), (55,1)], 4⟩,
    ⟨49, 55, 33, 37, [(55,1), (64,3), (27,-3), (36,-1), (91,-3), (54,1), (35,-1), (53,1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (38,-1), (56,1), (37,-1)], 4⟩,
    ⟨33, 37, 25, 28, [(37,-1), (55,1), (27,-3), (64,3), (36,-1), (54,1), (91,-3), (35,-1), (53,1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (38,-1), (56,1)], 4⟩,
    ⟨25, 28, 17, 19, [(56,1), (37,-1), (27,-3), (55,1), (36,-1), (64,3), (54,1), (35,-1), (91,-3), (53,1), (34,-1), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1), (57,1), (38,-1)], 4⟩,
    ⟨17, 19, 26, 29, [(38,-1), (57,1), (37,-1), (56,1), (27,-3), (36,-1), (55,1), (64,3), (35,-1), (54,1), (34,-1), (53,1), (91,-3), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1)], 4⟩]⟩

lemma phiCertifiedSegment228_checked : phiCertifiedSegment228.check=true := by decide +kernel

def phiCertifiedSegment229 : PhiCertifiedSegment :=
  ⟨(26/29), (9/10), 5, [
    ⟨26, 29, 53, 59, [(29,-1), (58,1), (38,-1), (57,1), (37,-1), (27,-3), (56,1), (36,-1), (55,1), (35,-1), (64,3), (54,1), (34,-1), (53,1), (33,-1), (62,1), (91,-3), (32,-1), (61,1), (31,-1), (60,1), (30,-1), (59,1)], 5⟩,
    ⟨53, 59, 9, 10, [(59,1), (29,-1), (58,1), (38,-1), (57,1), (37,-1), (27,-3), (56,1), (36,-1), (55,1), (35,-1), (64,3), (54,1), (34,-1), (53,1), (33,-1), (62,1), (32,-1), (91,-3), (61,1), (31,-1), (60,1), (30,-1)], 5⟩]⟩

lemma phiCertifiedSegment229_checked : phiCertifiedSegment229.check=true := by decide +kernel

def phiCertifiedSegment230 : PhiCertifiedSegment :=
  ⟨(9/10), (28/31), 4, [
    ⟨9, 10, 82, 91, [(30,-1), (60,1), (29,-1), (59,1), (38,-1), (58,1), (27,-3), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (64,3), (33,-1), (53,1), (32,-1), (62,1), (31,-1), (61,1), (91,-3)], 4⟩,
    ⟨82, 91, 55, 61, [(91,-3), (30,-1), (60,1), (29,-1), (59,1), (38,-1), (58,1), (27,-3), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (64,3), (33,-1), (53,1), (32,-1), (62,1), (31,-1), (61,1)], 4⟩,
    ⟨55, 61, 28, 31, [(61,1), (30,-1), (91,-3), (60,1), (29,-1), (59,1), (38,-1), (58,1), (27,-3), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (64,3), (33,-1), (53,1), (32,-1), (62,1), (31,-1)], 4⟩]⟩

lemma phiCertifiedSegment230_checked : phiCertifiedSegment230.check=true := by decide +kernel

def phiCertifiedSegment231 : PhiCertifiedSegment :=
  ⟨(28/31), (31/34), 5, [
    ⟨28, 31, 19, 21, [(31,-1), (62,1), (30,-1), (61,1), (29,-1), (60,1), (91,-3), (59,1), (38,-1), (27,-3), (58,1), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (33,-1), (64,3), (53,1), (32,-1)], 5⟩,
    ⟨19, 21, 48, 53, [(31,-1), (62,1), (30,-1), (61,1), (29,-1), (60,1), (91,-3), (38,-1), (59,1), (27,-3), (37,-1), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1), (54,1), (64,3), (32,-1), (53,1)], 5⟩,
    ⟨48, 53, 29, 32, [(53,1), (31,-1), (62,1), (30,-1), (61,1), (29,-1), (60,1), (38,-1), (91,-3), (59,1), (27,-3), (37,-1), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1), (54,1), (64,3), (32,-1)], 5⟩,
    ⟨29, 32, 49, 54, [(32,-1), (64,3), (53,1), (31,-1), (30,-1), (62,1), (29,-1), (61,1), (60,1), (38,-1), (27,-3), (59,1), (91,-3), (37,-1), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1), (54,1)], 5⟩,
    ⟨49, 54, 10, 11, [(54,1), (32,-1), (64,3), (53,1), (31,-1), (30,-1), (62,1), (29,-1), (61,1), (60,1), (38,-1), (27,-3), (59,1), (37,-1), (91,-3), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1)], 5⟩,
    ⟨10, 11, 51, 56, [(33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (64,3), (30,-1), (29,-1), (62,1), (61,1), (27,-3), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (91,-3), (35,-1), (57,1), (34,-1), (56,1)], 5⟩,
    ⟨51, 56, 31, 34, [(56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (64,3), (30,-1), (29,-1), (62,1), (61,1), (27,-3), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1), (91,-3), (57,1), (34,-1)], 5⟩]⟩

lemma phiCertifiedSegment231_checked : phiCertifiedSegment231.check=true := by decide +kernel

def phiCertifiedSegment232 : PhiCertifiedSegment :=
  ⟨(31/34), (83/91), 6, [
    ⟨31, 34, 83, 91, [(34,-1), (56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (30,-1), (64,3), (29,-1), (62,1), (27,-3), (61,1), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1), (57,1), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment232_checked : phiCertifiedSegment232.check=true := by decide +kernel

def phiCertifiedSegment233 : PhiCertifiedSegment :=
  ⟨(83/91), (11/12), 8, [
    ⟨83, 91, 52, 57, [(91,-3), (34,-1), (56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (30,-1), (64,3), (29,-1), (62,1), (27,-3), (61,1), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1), (57,1)], 8⟩,
    ⟨52, 57, 21, 23, [(57,1), (34,-1), (91,-3), (56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (30,-1), (64,3), (29,-1), (62,1), (27,-3), (61,1), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1)], 8⟩,
    ⟨21, 23, 53, 58, [(34,-1), (57,1), (91,-3), (33,-1), (56,1), (32,-1), (55,1), (31,-1), (54,1), (30,-1), (53,1), (64,3), (29,-1), (62,1), (27,-3), (38,-1), (61,1), (37,-1), (60,1), (36,-1), (59,1), (35,-1), (58,1)], 8⟩,
    ⟨53, 58, 32, 35, [(58,1), (34,-1), (57,1), (33,-1), (91,-3), (56,1), (32,-1), (55,1), (31,-1), (54,1), (30,-1), (53,1), (64,3), (29,-1), (62,1), (27,-3), (38,-1), (61,1), (37,-1), (60,1), (36,-1), (59,1), (35,-1)], 8⟩,
    ⟨32, 35, 54, 59, [(35,-1), (58,1), (34,-1), (57,1), (33,-1), (56,1), (91,-3), (32,-1), (55,1), (31,-1), (54,1), (30,-1), (53,1), (29,-1), (64,3), (27,-3), (62,1), (38,-1), (61,1), (37,-1), (60,1), (36,-1), (59,1)], 8⟩,
    ⟨54, 59, 11, 12, [(59,1), (35,-1), (58,1), (34,-1), (57,1), (33,-1), (56,1), (32,-1), (91,-3), (55,1), (31,-1), (54,1), (30,-1), (53,1), (29,-1), (64,3), (27,-3), (62,1), (38,-1), (61,1), (37,-1), (60,1), (36,-1)], 8⟩]⟩

lemma phiCertifiedSegment233_checked : phiCertifiedSegment233.check=true := by decide +kernel

def phiCertifiedSegment234 : PhiCertifiedSegment :=
  ⟨(11/12), (34/37), 7, [
    ⟨11, 12, 56, 61, [(36,-1), (60,1), (35,-1), (59,1), (34,-1), (58,1), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (55,1), (91,-3), (30,-1), (54,1), (29,-1), (53,1), (64,3), (27,-3), (38,-1), (62,1), (37,-1), (61,1)], 7⟩,
    ⟨56, 61, 34, 37, [(61,1), (36,-1), (60,1), (35,-1), (59,1), (34,-1), (58,1), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (55,1), (30,-1), (91,-3), (54,1), (29,-1), (53,1), (64,3), (27,-3), (38,-1), (62,1), (37,-1)], 7⟩]⟩

lemma phiCertifiedSegment234_checked : phiCertifiedSegment234.check=true := by decide +kernel

def phiCertifiedSegment235 : PhiCertifiedSegment :=
  ⟨(34/37), (23/25), 5, [
    ⟨34, 37, 57, 62, [(37,-1), (61,1), (36,-1), (60,1), (35,-1), (59,1), (34,-1), (58,1), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (55,1), (30,-1), (54,1), (91,-3), (29,-1), (53,1), (27,-3), (64,3), (38,-1), (62,1)], 5⟩,
    ⟨57, 62, 23, 25, [(62,1), (37,-1), (61,1), (36,-1), (60,1), (35,-1), (59,1), (34,-1), (58,1), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (55,1), (30,-1), (54,1), (29,-1), (91,-3), (53,1), (27,-3), (64,3), (38,-1)], 5⟩]⟩

lemma phiCertifiedSegment235_checked : phiCertifiedSegment235.check=true := by decide +kernel

def phiCertifiedSegment236 : PhiCertifiedSegment :=
  ⟨(23/25), (12/13), 6, [
    ⟨23, 25, 35, 38, [(37,-1), (62,1), (36,-1), (61,1), (35,-1), (60,1), (34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (31,-1), (56,1), (30,-1), (55,1), (29,-1), (54,1), (91,-3), (53,1), (27,-3), (64,3), (38,-1)], 6⟩,
    ⟨35, 38, 59, 64, [(38,-1), (37,-1), (62,1), (36,-1), (61,1), (35,-1), (60,1), (34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (31,-1), (56,1), (30,-1), (55,1), (29,-1), (54,1), (53,1), (91,-3), (27,-3), (64,3)], 6⟩,
    ⟨59, 64, 12, 13, [(64,3), (38,-1), (37,-1), (62,1), (36,-1), (61,1), (35,-1), (60,1), (34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (31,-1), (56,1), (30,-1), (55,1), (29,-1), (54,1), (53,1), (27,-3), (91,-3)], 6⟩]⟩

lemma phiCertifiedSegment236_checked : phiCertifiedSegment236.check=true := by decide +kernel

def phiCertifiedSegment237 : PhiCertifiedSegment :=
  ⟨(12/13), (25/27), 8, [
    ⟨12, 13, 49, 53, [(91,-3), (38,-1), (64,3), (37,-1), (36,-1), (62,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (29,-1), (55,1), (54,1), (27,-3), (53,1)], 8⟩,
    ⟨49, 53, 25, 27, [(53,1), (38,-1), (91,-3), (64,3), (37,-1), (36,-1), (62,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (29,-1), (55,1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment237_checked : phiCertifiedSegment237.check=true := by decide +kernel

def phiCertifiedSegment238 : PhiCertifiedSegment :=
  ⟨(25/27), (13/14), 3, [
    ⟨25, 27, 51, 55, [(27,-3), (54,1), (53,1), (38,-1), (37,-1), (64,3), (91,-3), (36,-1), (35,-1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (56,1), (55,1)], 3⟩,
    ⟨51, 55, 13, 14, [(55,1), (27,-3), (54,1), (53,1), (38,-1), (37,-1), (64,3), (36,-1), (91,-3), (35,-1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (56,1)], 3⟩]⟩

lemma phiCertifiedSegment238_checked : phiCertifiedSegment238.check=true := by decide +kernel

def phiCertifiedSegment239 : PhiCertifiedSegment :=
  ⟨(13/14), (14/15), 2, [
    ⟨13, 14, 53, 57, [(56,1), (27,-3), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (64,3), (35,-1), (91,-3), (34,-1), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1), (57,1)], 2⟩,
    ⟨53, 57, 27, 29, [(57,1), (56,1), (27,-3), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (64,3), (35,-1), (34,-1), (91,-3), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1)], 2⟩,
    ⟨27, 29, 55, 59, [(29,-1), (58,1), (57,1), (27,-3), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (64,3), (34,-1), (33,-1), (62,1), (91,-3), (32,-1), (61,1), (31,-1), (60,1), (30,-1), (59,1)], 2⟩,
    ⟨55, 59, 14, 15, [(59,1), (29,-1), (58,1), (57,1), (27,-3), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (64,3), (34,-1), (33,-1), (62,1), (32,-1), (91,-3), (61,1), (31,-1), (60,1), (30,-1)], 2⟩]⟩

lemma phiCertifiedSegment239_checked : phiCertifiedSegment239.check=true := by decide +kernel

def phiCertifiedSegment240 : PhiCertifiedSegment :=
  ⟨(14/15), (85/91), 3, [
    ⟨14, 15, 85, 91, [(30,-1), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (38,-1), (53,1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1), (61,1), (91,-3)], 3⟩]⟩

lemma phiCertifiedSegment240_checked : phiCertifiedSegment240.check=true := by decide +kernel

def phiCertifiedSegment241 : PhiCertifiedSegment :=
  ⟨(85/91), (31/33), 4, [
    ⟨85, 91, 57, 61, [(91,-3), (30,-1), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (38,-1), (53,1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1), (61,1)], 4⟩,
    ⟨57, 61, 29, 31, [(61,1), (30,-1), (91,-3), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (38,-1), (53,1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1)], 4⟩,
    ⟨29, 31, 15, 16, [(31,-1), (62,1), (30,-1), (61,1), (29,-1), (60,1), (91,-3), (59,1), (27,-3), (58,1), (57,1), (56,1), (55,1), (54,1), (38,-1), (53,1), (37,-1), (36,-1), (35,-1), (34,-1), (33,-1), (64,3), (32,-1)], 4⟩,
    ⟨15, 16, 31, 33, [(32,-1), (64,3), (31,-1), (30,-1), (62,1), (29,-1), (61,1), (60,1), (27,-3), (59,1), (91,-3), (58,1), (57,1), (56,1), (55,1), (38,-1), (54,1), (37,-1), (53,1), (36,-1), (35,-1), (34,-1), (33,-1)], 4⟩]⟩

lemma phiCertifiedSegment241_checked : phiCertifiedSegment241.check=true := by decide +kernel

def phiCertifiedSegment242 : PhiCertifiedSegment :=
  ⟨(31/33), (33/35), 6, [
    ⟨31, 33, 16, 17, [(33,-1), (32,-1), (31,-1), (64,3), (30,-1), (29,-1), (62,1), (61,1), (27,-3), (60,1), (59,1), (58,1), (91,-3), (57,1), (56,1), (55,1), (38,-1), (54,1), (37,-1), (53,1), (36,-1), (35,-1), (34,-1)], 6⟩,
    ⟨16, 17, 33, 35, [(34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (64,3), (29,-1), (62,1), (27,-3), (61,1), (60,1), (59,1), (58,1), (57,1), (91,-3), (56,1), (38,-1), (55,1), (37,-1), (54,1), (36,-1), (53,1), (35,-1)], 6⟩]⟩

lemma phiCertifiedSegment242_checked : phiCertifiedSegment242.check=true := by decide +kernel

def phiCertifiedSegment243 : PhiCertifiedSegment :=
  ⟨(33/35), (35/37), 5, [
    ⟨33, 35, 50, 53, [(35,-1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (56,1), (91,-3), (38,-1), (55,1), (37,-1), (54,1), (36,-1), (53,1)], 5⟩,
    ⟨50, 53, 17, 18, [(53,1), (35,-1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (56,1), (38,-1), (91,-3), (55,1), (37,-1), (54,1), (36,-1)], 5⟩,
    ⟨17, 18, 86, 91, [(36,-1), (54,1), (35,-1), (53,1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (38,-1), (56,1), (37,-1), (55,1), (91,-3)], 5⟩,
    ⟨86, 91, 52, 55, [(91,-3), (36,-1), (54,1), (35,-1), (53,1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (38,-1), (56,1), (37,-1), (55,1)], 5⟩,
    ⟨52, 55, 35, 37, [(55,1), (36,-1), (91,-3), (54,1), (35,-1), (53,1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (38,-1), (56,1), (37,-1)], 5⟩]⟩

lemma phiCertifiedSegment243_checked : phiCertifiedSegment243.check=true := by decide +kernel

def phiCertifiedSegment244 : PhiCertifiedSegment :=
  ⟨(35/37), (18/19), 2, [
    ⟨35, 37, 53, 56, [(37,-1), (55,1), (36,-1), (54,1), (91,-3), (35,-1), (53,1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (38,-1), (56,1)], 2⟩,
    ⟨53, 56, 18, 19, [(56,1), (37,-1), (55,1), (36,-1), (54,1), (35,-1), (91,-3), (53,1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (38,-1)], 2⟩]⟩

lemma phiCertifiedSegment244_checked : phiCertifiedSegment244.check=true := by decide +kernel

def phiCertifiedSegment245 : PhiCertifiedSegment :=
  ⟨(18/19), (20/21), 3, [
    ⟨18, 19, 55, 58, [(38,-1), (57,1), (37,-1), (56,1), (36,-1), (55,1), (35,-1), (54,1), (34,-1), (53,1), (91,-3), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1), (60,1), (59,1), (58,1)], 3⟩,
    ⟨55, 58, 56, 59, [(58,1), (38,-1), (57,1), (37,-1), (56,1), (36,-1), (55,1), (35,-1), (54,1), (34,-1), (53,1), (33,-1), (91,-3), (32,-1), (31,-1), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1), (60,1), (59,1)], 3⟩,
    ⟨56, 59, 19, 20, [(59,1), (58,1), (38,-1), (57,1), (37,-1), (56,1), (36,-1), (55,1), (35,-1), (54,1), (34,-1), (53,1), (33,-1), (32,-1), (91,-3), (31,-1), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1), (60,1)], 3⟩,
    ⟨19, 20, 58, 61, [(60,1), (59,1), (38,-1), (58,1), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (33,-1), (53,1), (32,-1), (31,-1), (91,-3), (30,-1), (29,-1), (27,-3), (64,3), (62,1), (61,1)], 3⟩,
    ⟨58, 61, 59, 62, [(61,1), (60,1), (59,1), (38,-1), (58,1), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (33,-1), (53,1), (32,-1), (31,-1), (30,-1), (91,-3), (29,-1), (27,-3), (64,3), (62,1)], 3⟩,
    ⟨59, 62, 20, 21, [(62,1), (61,1), (60,1), (59,1), (38,-1), (58,1), (37,-1), (57,1), (36,-1), (56,1), (35,-1), (55,1), (34,-1), (54,1), (33,-1), (53,1), (32,-1), (31,-1), (30,-1), (29,-1), (91,-3), (27,-3), (64,3)], 3⟩]⟩

lemma phiCertifiedSegment245_checked : phiCertifiedSegment245.check=true := by decide +kernel

def phiCertifiedSegment246 : PhiCertifiedSegment :=
  ⟨(20/21), (87/91), 4, [
    ⟨20, 21, 61, 64, [(62,1), (61,1), (60,1), (38,-1), (59,1), (37,-1), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1), (54,1), (32,-1), (53,1), (31,-1), (30,-1), (29,-1), (91,-3), (27,-3), (64,3)], 4⟩,
    ⟨61, 64, 21, 22, [(64,3), (62,1), (61,1), (60,1), (38,-1), (59,1), (37,-1), (58,1), (36,-1), (57,1), (35,-1), (56,1), (34,-1), (55,1), (33,-1), (54,1), (32,-1), (53,1), (31,-1), (30,-1), (29,-1), (27,-3), (91,-3)], 4⟩,
    ⟨21, 22, 87, 91, [(64,3), (62,1), (61,1), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1), (57,1), (34,-1), (56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (30,-1), (29,-1), (27,-3), (91,-3)], 4⟩]⟩

lemma phiCertifiedSegment246_checked : phiCertifiedSegment246.check=true := by decide +kernel

def phiCertifiedSegment247 : PhiCertifiedSegment :=
  ⟨(87/91), (22/23), 7, [
    ⟨87, 91, 22, 23, [(91,-3), (64,3), (62,1), (61,1), (38,-1), (60,1), (37,-1), (59,1), (36,-1), (58,1), (35,-1), (57,1), (34,-1), (56,1), (33,-1), (55,1), (32,-1), (54,1), (31,-1), (53,1), (30,-1), (29,-1), (27,-3)], 7⟩]⟩

lemma phiCertifiedSegment247_checked : phiCertifiedSegment247.check=true := by decide +kernel

def phiCertifiedSegment248 : PhiCertifiedSegment :=
  ⟨(22/23), (24/25), 8, [
    ⟨22, 23, 23, 24, [(91,-3), (64,3), (62,1), (38,-1), (61,1), (37,-1), (60,1), (36,-1), (59,1), (35,-1), (58,1), (34,-1), (57,1), (33,-1), (56,1), (32,-1), (55,1), (31,-1), (54,1), (30,-1), (53,1), (29,-1), (27,-3)], 8⟩,
    ⟨23, 24, 24, 25, [(91,-3), (64,3), (38,-1), (62,1), (37,-1), (61,1), (36,-1), (60,1), (35,-1), (59,1), (34,-1), (58,1), (33,-1), (57,1), (32,-1), (56,1), (31,-1), (55,1), (30,-1), (54,1), (29,-1), (53,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment248_checked : phiCertifiedSegment248.check=true := by decide +kernel

def phiCertifiedSegment249 : PhiCertifiedSegment :=
  ⟨(24/25), (25/26), 9, [
    ⟨24, 25, 25, 26, [(91,-3), (64,3), (38,-1), (37,-1), (62,1), (36,-1), (61,1), (35,-1), (60,1), (34,-1), (59,1), (33,-1), (58,1), (32,-1), (57,1), (31,-1), (56,1), (30,-1), (55,1), (29,-1), (54,1), (53,1), (27,-3)], 9⟩]⟩

lemma phiCertifiedSegment249_checked : phiCertifiedSegment249.check=true := by decide +kernel

def phiCertifiedSegment250 : PhiCertifiedSegment :=
  ⟨(25/26), (26/27), 8, [
    ⟨25, 26, 51, 53, [(91,-3), (38,-1), (64,3), (37,-1), (36,-1), (62,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (29,-1), (55,1), (54,1), (27,-3), (53,1)], 8⟩,
    ⟨51, 53, 26, 27, [(53,1), (38,-1), (91,-3), (64,3), (37,-1), (36,-1), (62,1), (35,-1), (61,1), (34,-1), (60,1), (33,-1), (59,1), (32,-1), (58,1), (31,-1), (57,1), (30,-1), (56,1), (29,-1), (55,1), (54,1), (27,-3)], 8⟩]⟩

lemma phiCertifiedSegment250_checked : phiCertifiedSegment250.check=true := by decide +kernel

def phiCertifiedSegment251 : PhiCertifiedSegment :=
  ⟨(26/27), (27/28), 3, [
    ⟨26, 27, 53, 55, [(27,-3), (54,1), (53,1), (38,-1), (37,-1), (64,3), (91,-3), (36,-1), (35,-1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (56,1), (55,1)], 3⟩,
    ⟨53, 55, 27, 28, [(55,1), (27,-3), (54,1), (53,1), (38,-1), (37,-1), (64,3), (36,-1), (91,-3), (35,-1), (62,1), (34,-1), (61,1), (33,-1), (60,1), (32,-1), (59,1), (31,-1), (58,1), (30,-1), (57,1), (29,-1), (56,1)], 3⟩]⟩

lemma phiCertifiedSegment251_checked : phiCertifiedSegment251.check=true := by decide +kernel

def phiCertifiedSegment252 : PhiCertifiedSegment :=
  ⟨(27/28), (88/91), 2, [
    ⟨27, 28, 55, 57, [(56,1), (27,-3), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (64,3), (35,-1), (91,-3), (34,-1), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1), (57,1)], 2⟩,
    ⟨55, 57, 28, 29, [(57,1), (56,1), (27,-3), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (64,3), (35,-1), (34,-1), (91,-3), (62,1), (33,-1), (61,1), (32,-1), (60,1), (31,-1), (59,1), (30,-1), (58,1), (29,-1)], 2⟩,
    ⟨28, 29, 57, 59, [(29,-1), (58,1), (57,1), (27,-3), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (64,3), (34,-1), (33,-1), (62,1), (91,-3), (32,-1), (61,1), (31,-1), (60,1), (30,-1), (59,1)], 2⟩,
    ⟨57, 59, 29, 30, [(59,1), (29,-1), (58,1), (57,1), (27,-3), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (64,3), (34,-1), (33,-1), (62,1), (32,-1), (91,-3), (61,1), (31,-1), (60,1), (30,-1)], 2⟩,
    ⟨29, 30, 88, 91, [(30,-1), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1), (61,1), (91,-3)], 2⟩]⟩

lemma phiCertifiedSegment252_checked : phiCertifiedSegment252.check=true := by decide +kernel

def phiCertifiedSegment253 : PhiCertifiedSegment :=
  ⟨(88/91), (32/33), 3, [
    ⟨88, 91, 59, 61, [(91,-3), (30,-1), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1), (61,1)], 3⟩,
    ⟨59, 61, 30, 31, [(61,1), (30,-1), (91,-3), (60,1), (29,-1), (59,1), (58,1), (27,-3), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (64,3), (33,-1), (32,-1), (62,1), (31,-1)], 3⟩,
    ⟨30, 31, 31, 32, [(31,-1), (62,1), (30,-1), (61,1), (29,-1), (60,1), (91,-3), (59,1), (27,-3), (58,1), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (33,-1), (64,3), (32,-1)], 3⟩,
    ⟨31, 32, 32, 33, [(32,-1), (64,3), (31,-1), (30,-1), (62,1), (29,-1), (61,1), (60,1), (27,-3), (59,1), (91,-3), (58,1), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (33,-1)], 3⟩]⟩

lemma phiCertifiedSegment253_checked : phiCertifiedSegment253.check=true := by decide +kernel

def phiCertifiedSegment254 : PhiCertifiedSegment :=
  ⟨(32/33), (33/34), 5, [
    ⟨32, 33, 33, 34, [(33,-1), (32,-1), (31,-1), (64,3), (30,-1), (29,-1), (62,1), (61,1), (27,-3), (60,1), (59,1), (58,1), (91,-3), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1)], 5⟩]⟩

lemma phiCertifiedSegment254_checked : phiCertifiedSegment254.check=true := by decide +kernel

def phiCertifiedSegment255 : PhiCertifiedSegment :=
  ⟨(33/34), (34/35), 4, [
    ⟨33, 34, 34, 35, [(34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (64,3), (29,-1), (62,1), (27,-3), (61,1), (60,1), (59,1), (58,1), (57,1), (91,-3), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1)], 4⟩]⟩

lemma phiCertifiedSegment255_checked : phiCertifiedSegment255.check=true := by decide +kernel

def phiCertifiedSegment256 : PhiCertifiedSegment :=
  ⟨(34/35), (36/37), 3, [
    ⟨34, 35, 35, 36, [(35,-1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (56,1), (91,-3), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1)], 3⟩,
    ⟨35, 36, 36, 37, [(36,-1), (35,-1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (64,3), (27,-3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (56,1), (55,1), (91,-3), (54,1), (53,1), (38,-1), (37,-1)], 3⟩]⟩

lemma phiCertifiedSegment256_checked : phiCertifiedSegment256.check=true := by decide +kernel

def phiCertifiedSegment258 : PhiCertifiedSegment :=
  ⟨(90/91), (1), 3, [
    ⟨90, 91, 1, 1, [(91,-3), (64,3), (62,1), (61,1), (60,1), (59,1), (58,1), (57,1), (56,1), (55,1), (54,1), (53,1), (38,-1), (37,-1), (36,-1), (35,-1), (34,-1), (33,-1), (32,-1), (31,-1), (30,-1), (29,-1), (27,-3)], 3⟩]⟩

lemma phiCertifiedSegment258_checked : phiCertifiedSegment258.check=true := by decide +kernel

def phiCertifiedSegments : List PhiCertifiedSegment :=
  [phiCertifiedSegment1,
   phiCertifiedSegment2,
   phiCertifiedSegment3,
   phiCertifiedSegment4,
   phiCertifiedSegment5,
   phiCertifiedSegment6,
   phiCertifiedSegment7,
   phiCertifiedSegment8,
   phiCertifiedSegment9,
   phiCertifiedSegment10,
   phiCertifiedSegment11,
   phiCertifiedSegment12,
   phiCertifiedSegment13,
   phiCertifiedSegment14,
   phiCertifiedSegment15,
   phiCertifiedSegment16,
   phiCertifiedSegment17,
   phiCertifiedSegment18,
   phiCertifiedSegment19,
   phiCertifiedSegment20,
   phiCertifiedSegment21,
   phiCertifiedSegment22,
   phiCertifiedSegment23,
   phiCertifiedSegment24,
   phiCertifiedSegment25,
   phiCertifiedSegment26,
   phiCertifiedSegment27,
   phiCertifiedSegment28,
   phiCertifiedSegment29,
   phiCertifiedSegment30,
   phiCertifiedSegment31,
   phiCertifiedSegment32,
   phiCertifiedSegment33,
   phiCertifiedSegment34,
   phiCertifiedSegment35,
   phiCertifiedSegment36,
   phiCertifiedSegment37,
   phiCertifiedSegment38,
   phiCertifiedSegment39,
   phiCertifiedSegment40,
   phiCertifiedSegment41,
   phiCertifiedSegment42,
   phiCertifiedSegment43,
   phiCertifiedSegment44,
   phiCertifiedSegment45,
   phiCertifiedSegment46,
   phiCertifiedSegment47,
   phiCertifiedSegment48,
   phiCertifiedSegment49,
   phiCertifiedSegment50,
   phiCertifiedSegment51,
   phiCertifiedSegment52,
   phiCertifiedSegment53,
   phiCertifiedSegment54,
   phiCertifiedSegment55,
   phiCertifiedSegment56,
   phiCertifiedSegment57,
   phiCertifiedSegment58,
   phiCertifiedSegment59,
   phiCertifiedSegment60,
   phiCertifiedSegment61,
   phiCertifiedSegment62,
   phiCertifiedSegment63,
   phiCertifiedSegment64,
   phiCertifiedSegment65,
   phiCertifiedSegment66,
   phiCertifiedSegment67,
   phiCertifiedSegment68,
   phiCertifiedSegment69,
   phiCertifiedSegment70,
   phiCertifiedSegment71,
   phiCertifiedSegment72,
   phiCertifiedSegment73,
   phiCertifiedSegment74,
   phiCertifiedSegment75,
   phiCertifiedSegment76,
   phiCertifiedSegment77,
   phiCertifiedSegment78,
   phiCertifiedSegment79,
   phiCertifiedSegment80,
   phiCertifiedSegment81,
   phiCertifiedSegment82,
   phiCertifiedSegment83,
   phiCertifiedSegment84,
   phiCertifiedSegment85,
   phiCertifiedSegment86,
   phiCertifiedSegment87,
   phiCertifiedSegment88,
   phiCertifiedSegment89,
   phiCertifiedSegment90,
   phiCertifiedSegment91,
   phiCertifiedSegment92,
   phiCertifiedSegment93,
   phiCertifiedSegment94,
   phiCertifiedSegment95,
   phiCertifiedSegment96,
   phiCertifiedSegment97,
   phiCertifiedSegment98,
   phiCertifiedSegment99,
   phiCertifiedSegment100,
   phiCertifiedSegment101,
   phiCertifiedSegment102,
   phiCertifiedSegment103,
   phiCertifiedSegment104,
   phiCertifiedSegment105,
   phiCertifiedSegment106,
   phiCertifiedSegment107,
   phiCertifiedSegment108,
   phiCertifiedSegment109,
   phiCertifiedSegment110,
   phiCertifiedSegment111,
   phiCertifiedSegment112,
   phiCertifiedSegment113,
   phiCertifiedSegment114,
   phiCertifiedSegment115,
   phiCertifiedSegment116,
   phiCertifiedSegment117,
   phiCertifiedSegment118,
   phiCertifiedSegment119,
   phiCertifiedSegment120,
   phiCertifiedSegment121,
   phiCertifiedSegment122,
   phiCertifiedSegment123,
   phiCertifiedSegment124,
   phiCertifiedSegment125,
   phiCertifiedSegment126,
   phiCertifiedSegment127,
   phiCertifiedSegment128,
   phiCertifiedSegment129,
   phiCertifiedSegment130,
   phiCertifiedSegment131,
   phiCertifiedSegment132,
   phiCertifiedSegment133,
   phiCertifiedSegment134,
   phiCertifiedSegment135,
   phiCertifiedSegment136,
   phiCertifiedSegment137,
   phiCertifiedSegment138,
   phiCertifiedSegment139,
   phiCertifiedSegment140,
   phiCertifiedSegment141,
   phiCertifiedSegment142,
   phiCertifiedSegment143,
   phiCertifiedSegment144,
   phiCertifiedSegment145,
   phiCertifiedSegment146,
   phiCertifiedSegment147,
   phiCertifiedSegment148,
   phiCertifiedSegment149,
   phiCertifiedSegment150,
   phiCertifiedSegment151,
   phiCertifiedSegment152,
   phiCertifiedSegment153,
   phiCertifiedSegment154,
   phiCertifiedSegment155,
   phiCertifiedSegment156,
   phiCertifiedSegment157,
   phiCertifiedSegment158,
   phiCertifiedSegment159,
   phiCertifiedSegment160,
   phiCertifiedSegment161,
   phiCertifiedSegment162,
   phiCertifiedSegment163,
   phiCertifiedSegment164,
   phiCertifiedSegment165,
   phiCertifiedSegment166,
   phiCertifiedSegment167,
   phiCertifiedSegment168,
   phiCertifiedSegment169,
   phiCertifiedSegment170,
   phiCertifiedSegment171,
   phiCertifiedSegment172,
   phiCertifiedSegment173,
   phiCertifiedSegment174,
   phiCertifiedSegment175,
   phiCertifiedSegment176,
   phiCertifiedSegment177,
   phiCertifiedSegment178,
   phiCertifiedSegment179,
   phiCertifiedSegment180,
   phiCertifiedSegment181,
   phiCertifiedSegment182,
   phiCertifiedSegment183,
   phiCertifiedSegment184,
   phiCertifiedSegment185,
   phiCertifiedSegment186,
   phiCertifiedSegment187,
   phiCertifiedSegment188,
   phiCertifiedSegment189,
   phiCertifiedSegment190,
   phiCertifiedSegment191,
   phiCertifiedSegment192,
   phiCertifiedSegment193,
   phiCertifiedSegment194,
   phiCertifiedSegment195,
   phiCertifiedSegment196,
   phiCertifiedSegment197,
   phiCertifiedSegment198,
   phiCertifiedSegment199,
   phiCertifiedSegment200,
   phiCertifiedSegment201,
   phiCertifiedSegment202,
   phiCertifiedSegment203,
   phiCertifiedSegment204,
   phiCertifiedSegment205,
   phiCertifiedSegment206,
   phiCertifiedSegment207,
   phiCertifiedSegment208,
   phiCertifiedSegment209,
   phiCertifiedSegment210,
   phiCertifiedSegment211,
   phiCertifiedSegment212,
   phiCertifiedSegment213,
   phiCertifiedSegment214,
   phiCertifiedSegment215,
   phiCertifiedSegment216,
   phiCertifiedSegment217,
   phiCertifiedSegment218,
   phiCertifiedSegment219,
   phiCertifiedSegment220,
   phiCertifiedSegment221,
   phiCertifiedSegment222,
   phiCertifiedSegment223,
   phiCertifiedSegment224,
   phiCertifiedSegment225,
   phiCertifiedSegment226,
   phiCertifiedSegment227,
   phiCertifiedSegment228,
   phiCertifiedSegment229,
   phiCertifiedSegment230,
   phiCertifiedSegment231,
   phiCertifiedSegment232,
   phiCertifiedSegment233,
   phiCertifiedSegment234,
   phiCertifiedSegment235,
   phiCertifiedSegment236,
   phiCertifiedSegment237,
   phiCertifiedSegment238,
   phiCertifiedSegment239,
   phiCertifiedSegment240,
   phiCertifiedSegment241,
   phiCertifiedSegment242,
   phiCertifiedSegment243,
   phiCertifiedSegment244,
   phiCertifiedSegment245,
   phiCertifiedSegment246,
   phiCertifiedSegment247,
   phiCertifiedSegment248,
   phiCertifiedSegment249,
   phiCertifiedSegment250,
   phiCertifiedSegment251,
   phiCertifiedSegment252,
   phiCertifiedSegment253,
   phiCertifiedSegment254,
   phiCertifiedSegment255,
   phiCertifiedSegment256,
   phiCertifiedSegment258]

lemma phiCertifiedSegments_checked :
    phiCertifiedSegments.all PhiCertifiedSegment.check=true := by
  simp only [phiCertifiedSegments, List.all_cons, List.all_nil,
    phiCertifiedSegment1_checked,
    phiCertifiedSegment2_checked,
    phiCertifiedSegment3_checked,
    phiCertifiedSegment4_checked,
    phiCertifiedSegment5_checked,
    phiCertifiedSegment6_checked,
    phiCertifiedSegment7_checked,
    phiCertifiedSegment8_checked,
    phiCertifiedSegment9_checked,
    phiCertifiedSegment10_checked,
    phiCertifiedSegment11_checked,
    phiCertifiedSegment12_checked,
    phiCertifiedSegment13_checked,
    phiCertifiedSegment14_checked,
    phiCertifiedSegment15_checked,
    phiCertifiedSegment16_checked,
    phiCertifiedSegment17_checked,
    phiCertifiedSegment18_checked,
    phiCertifiedSegment19_checked,
    phiCertifiedSegment20_checked,
    phiCertifiedSegment21_checked,
    phiCertifiedSegment22_checked,
    phiCertifiedSegment23_checked,
    phiCertifiedSegment24_checked,
    phiCertifiedSegment25_checked,
    phiCertifiedSegment26_checked,
    phiCertifiedSegment27_checked,
    phiCertifiedSegment28_checked,
    phiCertifiedSegment29_checked,
    phiCertifiedSegment30_checked,
    phiCertifiedSegment31_checked,
    phiCertifiedSegment32_checked,
    phiCertifiedSegment33_checked,
    phiCertifiedSegment34_checked,
    phiCertifiedSegment35_checked,
    phiCertifiedSegment36_checked,
    phiCertifiedSegment37_checked,
    phiCertifiedSegment38_checked,
    phiCertifiedSegment39_checked,
    phiCertifiedSegment40_checked,
    phiCertifiedSegment41_checked,
    phiCertifiedSegment42_checked,
    phiCertifiedSegment43_checked,
    phiCertifiedSegment44_checked,
    phiCertifiedSegment45_checked,
    phiCertifiedSegment46_checked,
    phiCertifiedSegment47_checked,
    phiCertifiedSegment48_checked,
    phiCertifiedSegment49_checked,
    phiCertifiedSegment50_checked,
    phiCertifiedSegment51_checked,
    phiCertifiedSegment52_checked,
    phiCertifiedSegment53_checked,
    phiCertifiedSegment54_checked,
    phiCertifiedSegment55_checked,
    phiCertifiedSegment56_checked,
    phiCertifiedSegment57_checked,
    phiCertifiedSegment58_checked,
    phiCertifiedSegment59_checked,
    phiCertifiedSegment60_checked,
    phiCertifiedSegment61_checked,
    phiCertifiedSegment62_checked,
    phiCertifiedSegment63_checked,
    phiCertifiedSegment64_checked,
    phiCertifiedSegment65_checked,
    phiCertifiedSegment66_checked,
    phiCertifiedSegment67_checked,
    phiCertifiedSegment68_checked,
    phiCertifiedSegment69_checked,
    phiCertifiedSegment70_checked,
    phiCertifiedSegment71_checked,
    phiCertifiedSegment72_checked,
    phiCertifiedSegment73_checked,
    phiCertifiedSegment74_checked,
    phiCertifiedSegment75_checked,
    phiCertifiedSegment76_checked,
    phiCertifiedSegment77_checked,
    phiCertifiedSegment78_checked,
    phiCertifiedSegment79_checked,
    phiCertifiedSegment80_checked,
    phiCertifiedSegment81_checked,
    phiCertifiedSegment82_checked,
    phiCertifiedSegment83_checked,
    phiCertifiedSegment84_checked,
    phiCertifiedSegment85_checked,
    phiCertifiedSegment86_checked,
    phiCertifiedSegment87_checked,
    phiCertifiedSegment88_checked,
    phiCertifiedSegment89_checked,
    phiCertifiedSegment90_checked,
    phiCertifiedSegment91_checked,
    phiCertifiedSegment92_checked,
    phiCertifiedSegment93_checked,
    phiCertifiedSegment94_checked,
    phiCertifiedSegment95_checked,
    phiCertifiedSegment96_checked,
    phiCertifiedSegment97_checked,
    phiCertifiedSegment98_checked,
    phiCertifiedSegment99_checked,
    phiCertifiedSegment100_checked,
    phiCertifiedSegment101_checked,
    phiCertifiedSegment102_checked,
    phiCertifiedSegment103_checked,
    phiCertifiedSegment104_checked,
    phiCertifiedSegment105_checked,
    phiCertifiedSegment106_checked,
    phiCertifiedSegment107_checked,
    phiCertifiedSegment108_checked,
    phiCertifiedSegment109_checked,
    phiCertifiedSegment110_checked,
    phiCertifiedSegment111_checked,
    phiCertifiedSegment112_checked,
    phiCertifiedSegment113_checked,
    phiCertifiedSegment114_checked,
    phiCertifiedSegment115_checked,
    phiCertifiedSegment116_checked,
    phiCertifiedSegment117_checked,
    phiCertifiedSegment118_checked,
    phiCertifiedSegment119_checked,
    phiCertifiedSegment120_checked,
    phiCertifiedSegment121_checked,
    phiCertifiedSegment122_checked,
    phiCertifiedSegment123_checked,
    phiCertifiedSegment124_checked,
    phiCertifiedSegment125_checked,
    phiCertifiedSegment126_checked,
    phiCertifiedSegment127_checked,
    phiCertifiedSegment128_checked,
    phiCertifiedSegment129_checked,
    phiCertifiedSegment130_checked,
    phiCertifiedSegment131_checked,
    phiCertifiedSegment132_checked,
    phiCertifiedSegment133_checked,
    phiCertifiedSegment134_checked,
    phiCertifiedSegment135_checked,
    phiCertifiedSegment136_checked,
    phiCertifiedSegment137_checked,
    phiCertifiedSegment138_checked,
    phiCertifiedSegment139_checked,
    phiCertifiedSegment140_checked,
    phiCertifiedSegment141_checked,
    phiCertifiedSegment142_checked,
    phiCertifiedSegment143_checked,
    phiCertifiedSegment144_checked,
    phiCertifiedSegment145_checked,
    phiCertifiedSegment146_checked,
    phiCertifiedSegment147_checked,
    phiCertifiedSegment148_checked,
    phiCertifiedSegment149_checked,
    phiCertifiedSegment150_checked,
    phiCertifiedSegment151_checked,
    phiCertifiedSegment152_checked,
    phiCertifiedSegment153_checked,
    phiCertifiedSegment154_checked,
    phiCertifiedSegment155_checked,
    phiCertifiedSegment156_checked,
    phiCertifiedSegment157_checked,
    phiCertifiedSegment158_checked,
    phiCertifiedSegment159_checked,
    phiCertifiedSegment160_checked,
    phiCertifiedSegment161_checked,
    phiCertifiedSegment162_checked,
    phiCertifiedSegment163_checked,
    phiCertifiedSegment164_checked,
    phiCertifiedSegment165_checked,
    phiCertifiedSegment166_checked,
    phiCertifiedSegment167_checked,
    phiCertifiedSegment168_checked,
    phiCertifiedSegment169_checked,
    phiCertifiedSegment170_checked,
    phiCertifiedSegment171_checked,
    phiCertifiedSegment172_checked,
    phiCertifiedSegment173_checked,
    phiCertifiedSegment174_checked,
    phiCertifiedSegment175_checked,
    phiCertifiedSegment176_checked,
    phiCertifiedSegment177_checked,
    phiCertifiedSegment178_checked,
    phiCertifiedSegment179_checked,
    phiCertifiedSegment180_checked,
    phiCertifiedSegment181_checked,
    phiCertifiedSegment182_checked,
    phiCertifiedSegment183_checked,
    phiCertifiedSegment184_checked,
    phiCertifiedSegment185_checked,
    phiCertifiedSegment186_checked,
    phiCertifiedSegment187_checked,
    phiCertifiedSegment188_checked,
    phiCertifiedSegment189_checked,
    phiCertifiedSegment190_checked,
    phiCertifiedSegment191_checked,
    phiCertifiedSegment192_checked,
    phiCertifiedSegment193_checked,
    phiCertifiedSegment194_checked,
    phiCertifiedSegment195_checked,
    phiCertifiedSegment196_checked,
    phiCertifiedSegment197_checked,
    phiCertifiedSegment198_checked,
    phiCertifiedSegment199_checked,
    phiCertifiedSegment200_checked,
    phiCertifiedSegment201_checked,
    phiCertifiedSegment202_checked,
    phiCertifiedSegment203_checked,
    phiCertifiedSegment204_checked,
    phiCertifiedSegment205_checked,
    phiCertifiedSegment206_checked,
    phiCertifiedSegment207_checked,
    phiCertifiedSegment208_checked,
    phiCertifiedSegment209_checked,
    phiCertifiedSegment210_checked,
    phiCertifiedSegment211_checked,
    phiCertifiedSegment212_checked,
    phiCertifiedSegment213_checked,
    phiCertifiedSegment214_checked,
    phiCertifiedSegment215_checked,
    phiCertifiedSegment216_checked,
    phiCertifiedSegment217_checked,
    phiCertifiedSegment218_checked,
    phiCertifiedSegment219_checked,
    phiCertifiedSegment220_checked,
    phiCertifiedSegment221_checked,
    phiCertifiedSegment222_checked,
    phiCertifiedSegment223_checked,
    phiCertifiedSegment224_checked,
    phiCertifiedSegment225_checked,
    phiCertifiedSegment226_checked,
    phiCertifiedSegment227_checked,
    phiCertifiedSegment228_checked,
    phiCertifiedSegment229_checked,
    phiCertifiedSegment230_checked,
    phiCertifiedSegment231_checked,
    phiCertifiedSegment232_checked,
    phiCertifiedSegment233_checked,
    phiCertifiedSegment234_checked,
    phiCertifiedSegment235_checked,
    phiCertifiedSegment236_checked,
    phiCertifiedSegment237_checked,
    phiCertifiedSegment238_checked,
    phiCertifiedSegment239_checked,
    phiCertifiedSegment240_checked,
    phiCertifiedSegment241_checked,
    phiCertifiedSegment242_checked,
    phiCertifiedSegment243_checked,
    phiCertifiedSegment244_checked,
    phiCertifiedSegment245_checked,
    phiCertifiedSegment246_checked,
    phiCertifiedSegment247_checked,
    phiCertifiedSegment248_checked,
    phiCertifiedSegment249_checked,
    phiCertifiedSegment250_checked,
    phiCertifiedSegment251_checked,
    phiCertifiedSegment252_checked,
    phiCertifiedSegment253_checked,
    phiCertifiedSegment254_checked,
    phiCertifiedSegment255_checked,
    phiCertifiedSegment256_checked,
    phiCertifiedSegment258_checked, Bool.and_self]

end ZudilinZeta
end

-- Component: PhiRegularity
section
open Set MeasureTheory ZudilinZeta

private lemma sigma_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) : IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  obtain ⟨L, hL, rfl⟩ := ht
  simp only [iUnion_inter, inter_iUnion]
  apply isSigmaCompact_iUnion
  intro n
  apply isSigmaCompact_iUnion
  intro m
  exact ((hK m).inter (hL n)).isSigmaCompact

private lemma sigma_locallyClosed {s : Set (ℝ × ℝ)} (hs : IsLocallyClosed s) :
    IsSigmaCompact s := by
  letI : LocallyCompactSpace s := hs.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

private lemma sigma_measurable {s : Set ℝ} (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

private def CompactFibers (f : ℝ × ℝ → ℤ) : Prop :=
  ∀ k : ℤ, IsSigmaCompact {z | f z = k}

private lemma compactFibers_const (c : ℤ) : CompactFibers (fun _ => c) := by
  intro k
  by_cases h : c = k
  · simpa [h] using (isSigmaCompact_univ : IsSigmaCompact (univ : Set (ℝ × ℝ)))
  · simp [h]

private lemma compactFibers_op {f g : ℝ × ℝ → ℤ}
    (hf : CompactFibers f) (hg : CompactFibers g) (op : ℤ → ℤ → ℤ) :
    CompactFibers (fun z => op (f z) (g z)) := by
  intro k
  have heq : {z | op (f z) (g z) = k} =
      ⋃ p : {p : ℤ × ℤ // op p.1 p.2 = k}, {z | f z = p.1.1} ∩ {z | g z = p.1.2} := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨(f z, g z), h⟩, rfl, rfl⟩
    · rintro ⟨p, hf, hg⟩
      simpa only [hf, hg] using p.2
  rw [heq]
  exact isSigmaCompact_iUnion _ fun p => sigma_inter (hf p.1.1) (hg p.1.2)

private lemma compactFibers_floor {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    CompactFibers (fun z => ⌊f z⌋) := by
  intro k
  have heq : {z | ⌊f z⌋ = k} = {z | (k : ℝ) ≤ f z} ∩ {z | f z < (k : ℝ) + 1} := by
    ext z
    simp only [mem_setOf_eq, mem_inter_iff, Int.floor_eq_iff]
  rw [heq]
  apply sigma_locallyClosed
  exact ((isClosed_le continuous_const hf).isLocallyClosed).inter
    ((isOpen_lt hf continuous_const).isLocallyClosed)

private lemma compactFibers_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℤ)
    (hf : ∀ i ∈ s, CompactFibers (f i)) : CompactFibers (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using compactFibers_const 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact compactFibers_op (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (· + ·)

private lemma phiExpr_compactFibers (P : Params) : CompactFibers (fun z => phiExpr P z.1 z.2) := by
  unfold phiExpr
  apply compactFibers_op _ _ (· + ·)
  · apply compactFibers_sum
    intro j hj
    repeat' first | apply compactFibers_op _ _ (· - ·)
                  | apply compactFibers_op _ _ (· + ·)
                  | apply compactFibers_op _ _ (· * ·)
                  | apply compactFibers_const
                  | apply compactFibers_floor
    all_goals fun_prop
  · apply compactFibers_sum
    intro j hj
    repeat' first | apply compactFibers_op _ _ (· - ·)
                  | apply compactFibers_floor
    all_goals fun_prop

-- The following floor-superadditivity proof reuses the argument in the accepted
-- Prove2Me submission c74c01b0-dbc0-4054-acf6-232df78455ed (cm_beta).
private lemma phiExpr_nonneg (P : Params) (x y : ℝ) : 0 ≤ phiExpr P x y := by
  have h1 (e0 ej : ℝ) :
      0 ≤ ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ := by
    have ha : ⌊(e0 - ej) * x - y⌋ + ⌊ej * x⌋ ≤ ⌊e0 * x - y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le ((e0 - ej) * x - y), Int.floor_le (ej * x)]
    have hb : ⌊ej * x⌋ + ⌊y - ej * x⌋ ≤ ⌊y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le (ej * x)]
    omega
  have h2 (e0 ej : ℝ) :
      0 ≤ ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ := by
    have h : ⌊y - ej * x⌋ + ⌊(e0 - ej) * x - y⌋ ≤ ⌊(e0 - 2 * ej) * x⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le ((e0 - ej) * x - y)]
    omega
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => h1 _ _))
    (Finset.sum_nonneg (fun _ _ => h2 _ _))

private lemma phiExpr_bddBelow (P : Params) (x : ℝ) :
    BddBelow (phiExpr P x '' Ico (0 : ℝ) 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, _, rfl⟩
  exact phiExpr_nonneg P x y

private lemma phi_measurable (P : Params) : Measurable (phi P) := by
  apply measurable_of_Iic
  intro k
  let s : Set (ℝ × ℝ) := {z | z.2 ∈ Ico (0 : ℝ) 1 ∧ phiExpr P z.1 z.2 ≤ k}
  have hf : IsSigmaCompact {z : ℝ × ℝ | phiExpr P z.1 z.2 ≤ k} := by
    have heq : {z : ℝ × ℝ | phiExpr P z.1 z.2 ≤ k} =
        ⋃ a : {a : ℤ // a ≤ k}, {z | phiExpr P z.1 z.2 = a.1} := by
      ext z
      simp only [mem_setOf_eq, mem_iUnion]
      exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨a, h⟩ => h ▸ a.2⟩
    rw [heq]
    exact isSigmaCompact_iUnion _ (fun a => phiExpr_compactFibers P a.1)
  have hs : IsSigmaCompact s := by
    apply sigma_inter _ hf
    apply sigma_locallyClosed
    exact ((isClosed_le continuous_const continuous_snd).isLocallyClosed).inter
      ((isOpen_lt continuous_snd continuous_const).isLocallyClosed)
  have heq : phi P ⁻¹' Iic k = Prod.fst '' s := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := Int.csInf_mem
        (show (phiExpr P x '' Ico (0 : ℝ) 1).Nonempty from ⟨_, 0, ⟨le_rfl, one_pos⟩, rfl⟩)
        (phiExpr_bddBelow P x)
      exact ⟨(x, y), ⟨hy, he.trans_le hx⟩, rfl⟩
    · rintro ⟨⟨a, y⟩, hy, rfl⟩
      exact (csInf_le (phiExpr_bddBelow P a) ⟨y, hy.1, rfl⟩).trans hy.2
  rw [heq]
  exact sigma_measurable (hs.image continuous_fst)

private lemma phi_bounded (P : Params) (x : ℝ) :
    phi P x ≤ 2 * ((Finset.Icc 1 P.r).card : ℤ) + (Finset.Icc (P.r + 1) P.q).card := by
  have h1 (e0 ej y : ℝ) :
      ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ ≤ 2 := by
    have ha := Int.le_floor_add_floor ((e0 - ej) * x - y) (ej * x)
    have hb := Int.le_floor_add_floor (ej * x) (y - ej * x)
    rw [show (e0 - ej) * x - y + ej * x = e0 * x - y by ring] at ha
    rw [show ej * x + (y - ej * x) = y by ring] at hb
    omega
  have h2 (e0 ej y : ℝ) :
      ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ ≤ 1 := by
    have h := Int.le_floor_add_floor (y - ej * x) ((e0 - ej) * x - y)
    rw [show y - ej * x + ((e0 - ej) * x - y) = (e0 - 2 * ej) * x by ring] at h
    omega
  apply (csInf_le (phiExpr_bddBelow P x) (show phiExpr P x 0 ∈ _ from
    ⟨0, ⟨le_rfl, one_pos⟩, rfl⟩)).trans
  have hsum := add_le_add (Finset.sum_le_sum (s := Finset.Icc 1 P.r) (fun j _ => h1 (P.eta 0) (P.eta j) 0))
    (Finset.sum_le_sum (s := Finset.Icc (P.r + 1) P.q) (fun j _ => h2 (P.eta 0) (P.eta j) 0))
  simpa [phiExpr, mul_comm] using hsum

private lemma eta_le_last (P : Params) (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) : P.eta j ≤ P.eta P.q := by
  have hm (k : ℕ) : ∀ i, 1 ≤ i → i + k ≤ P.q → P.eta i ≤ P.eta (i + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i hi hik
      have h1 := ih i hi (by omega)
      have h2 := P.eta_mono (i + k) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      simpa only [Nat.add_assoc] using h1.trans h2
  have h := hm (P.q - j) j (Finset.mem_Icc.mp hj).1 (by have := (Finset.mem_Icc.mp hj).2; omega)
  simpa only [Nat.add_sub_of_le (Finset.mem_Icc.mp hj).2] using h

private lemma phi_zero_near_zero (P : Params) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : (P.eta 0 : ℝ) * x < 1) : phi P x = 0 := by
  have hq : 0 ≤ (P.eta P.q : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hq2 : 2 * ((P.eta P.q : ℝ) * x) ≤ (P.eta 0 : ℝ) * x := by
    have he : 2 * (P.eta P.q : ℝ) ≤ P.eta 0 := by exact_mod_cast P.eta_lt.le
    nlinarith [mul_le_mul_of_nonneg_right he hx]
  have hy : (P.eta P.q : ℝ) * x ∈ Ico (0 : ℝ) 1 := ⟨hq, by linarith⟩
  have hfy : ⌊(P.eta P.q : ℝ) * x⌋ = 0 := Int.floor_eq_zero_iff.mpr hy
  have hf0 : ⌊(P.eta 0 : ℝ) * x - (P.eta P.q : ℝ) * x⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  have hterms (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) :
      (⌊(P.eta P.q : ℝ) * x - (P.eta j : ℝ) * x⌋ = 0) ∧
      (⌊((P.eta 0 : ℝ) - (P.eta j : ℝ)) * x - (P.eta P.q : ℝ) * x⌋ = 0) ∧
      (⌊(P.eta j : ℝ) * x⌋ = 0) ∧
      (⌊((P.eta 0 : ℝ) - 2 * (P.eta j : ℝ)) * x⌋ = 0) := by
    have hja : 0 ≤ (P.eta j : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
    have hjb : (P.eta j : ℝ) * x ≤ (P.eta P.q : ℝ) * x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast eta_le_last P j hj) hx
    refine ⟨Int.floor_eq_zero_iff.mpr ?_, Int.floor_eq_zero_iff.mpr ?_,
      Int.floor_eq_zero_iff.mpr ?_, Int.floor_eq_zero_iff.mpr ?_⟩ <;>
      constructor <;> nlinarith
  have he : phiExpr P x ((P.eta P.q : ℝ) * x) = 0 := by
    unfold phiExpr
    refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add (0 : ℤ))
    · apply Finset.sum_eq_zero
      intro j hj
      have hj' : j ∈ Finset.Icc 1 P.q := by
        have := Finset.mem_Icc.mp hj
        have := P.q_ge
        apply Finset.mem_Icc.mpr
        omega
      obtain ⟨ha, hb, hc, _⟩ := hterms j hj'
      simp only [hfy, hf0, ha, hb, hc]
      norm_num
    · apply Finset.sum_eq_zero
      intro j hj
      have hj' : j ∈ Finset.Icc 1 P.q := by
        have := Finset.mem_Icc.mp hj
        apply Finset.mem_Icc.mpr
        omega
      obtain ⟨ha, hb, _, hc⟩ := hterms j hj'
      simp only [ha, hb, hc]
      norm_num
  exact le_antisymm ((csInf_le (phiExpr_bddBelow P x) ⟨_, hy, rfl⟩).trans_eq he)
    ((zudilin_phi_nonneg_periodic P).1 x)

private lemma phi_weighted_integrable (P : Params) :
    IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioi 0) := by
  let δ : ℝ := 1 / ((P.eta 0 : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : (P.eta 0 : ℝ) * δ < 1 := by
    dsimp [δ]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  let B : ℝ := 2 * ((Finset.Icc 1 P.r).card : ℝ) + (Finset.Icc (P.r + 1) P.q).card
  have hb (x : ℝ) : (phi P x : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast phi_bounded P x
  have hnonneg (x : ℝ) : 0 ≤ (phi P x : ℝ) := by
    exact_mod_cast (zudilin_phi_nonneg_periodic P).1 x
  have hmeas : Measurable (fun x : ℝ => (phi P x : ℝ) / x ^ 2) := by
    exact ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (phi_measurable P)).div
      (measurable_id.pow_const 2)
  have htail : IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioi δ) := by
    have hbase : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi δ) := by
      simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hδ)
    have hdom := hbase.const_mul B
    apply hdom.mono' hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnonneg x) (sq_nonneg x)), mul_one_div]
    exact div_le_div_of_nonneg_right (hb x) (sq_nonneg x)
  have hhead : IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioc 0 δ) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 δ)).congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hz := phi_zero_near_zero P hx.1.le
      ((mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg _)).trans_lt hδ1)
    simp only [hz, Int.cast_zero, zero_div]
  simpa only [Ioc_union_Ioi_eq_Ioi hδ.le] using hhead.union htail

lemma ZudilinZeta.phi_weighted_integrableOn (P : Params) :
    IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioi 0) :=
  phi_weighted_integrable P
end

-- Component: WeightedIntervalBounds
section
open Set MeasureTheory

namespace ZudilinZeta

lemma integral_inv_sq_interval (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ x in a..b, 1/x^2)=1/a-1/b := by
  have hh := integral_zpow (a:=a) (b:=b) (n:=(-2 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha hb⟩)
  norm_num only [zpow_neg, zpow_ofNat, show (-2 : ℤ)+1 = -1 by norm_num,
    zpow_neg_one, Int.cast_neg, Int.cast_one, div_neg, div_one] at hh
  simpa only [one_div, neg_sub, pow_one] using hh

lemma intervalIntegrable_inv_sq (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    IntervalIntegrable (fun x : ℝ => 1/x^2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuousOn_id.pow 2)
  intro x hx
  exact pow_ne_zero 2 (ne_of_gt ((lt_min ha hb).trans_le hx.1))

structure WeightedRationalInterval where
  lower : ℚ
  upper : ℚ
  weight : ℤ
deriving DecidableEq

def WeightedRationalInterval.mass (c : WeightedRationalInterval) : ℚ :=
  c.weight*(1/c.lower-1/c.upper)

def intervalsOrderedCheck (a : ℚ) : List WeightedRationalInterval → Bool
  | [] => true
  | c::L => decide (a≤c.lower ∧ c.lower≤c.upper) && intervalsOrderedCheck c.upper L

lemma weighted_interval_lower_ae (P : Params) (c : WeightedRationalInterval)
    (hl : (0 : ℝ)<c.lower) (hlu : c.lower≤c.upper)
    (hc : ∀ᵐ x : ℝ, (c.lower : ℝ)<x → x<(c.upper : ℝ) → c.weight≤phi P x) :
    (c.mass : ℝ) ≤ ∫ x in (c.lower : ℝ)..(c.upper : ℝ), (phi P x : ℝ)/x^2 := by
  have hlu' : (c.lower : ℝ)≤c.upper := by exact_mod_cast hlu
  have hu : (0 : ℝ)<c.upper := hl.trans_le hlu'
  have hbase := (intervalIntegrable_inv_sq c.lower c.upper hl hu).const_mul (c.weight : ℝ)
  have hphi : IntervalIntegrable (fun x : ℝ => (phi P x : ℝ)/x^2)
      volume (c.lower : ℝ) (c.upper : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hlu').mpr
    apply (phi_weighted_integrableOn P).mono_set
    intro x hx
    exact hl.trans hx.1
  have hcmp : (∫ x in (c.lower : ℝ)..(c.upper : ℝ), (c.weight : ℝ)*(1/x^2)) ≤
      ∫ x in (c.lower : ℝ)..(c.upper : ℝ), (phi P x : ℝ)/x^2 := by
    apply intervalIntegral.integral_mono_ae_restrict hlu' hbase hphi
    filter_upwards [ae_restrict_of_ae hc,
      ae_restrict_of_ae (volume.ae_ne (c.lower : ℝ)),
      ae_restrict_of_ae (volume.ae_ne (c.upper : ℝ)),
      ae_restrict_mem measurableSet_Icc] with x hx hxl hxu hmem
    have hh := hx (lt_of_le_of_ne hmem.1 (Ne.symm hxl))
      (lt_of_le_of_ne hmem.2 hxu)
    have hle : (c.weight : ℝ)≤phi P x := by exact_mod_cast hh
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hle (sq_nonneg x)
  rw [intervalIntegral.integral_const_mul, integral_inv_sq_interval _ _ hl hu] at hcmp
  simpa only [WeightedRationalInterval.mass, Rat.cast_mul, Rat.cast_intCast,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one] using hcmp

lemma weighted_intervals_lower_tail_ae (P : Params) (L : List WeightedRationalInterval)
    (a : ℚ) (ha : 0<a) (hord : intervalsOrderedCheck a L=true)
    (hc : ∀ c∈L, ∀ᵐ x : ℝ, (c.lower : ℝ)<x → x<(c.upper : ℝ) → c.weight≤phi P x) :
    (((L.map WeightedRationalInterval.mass).sum : ℚ) : ℝ) ≤
      ∫ x in Ioi (a : ℝ), (phi P x : ℝ)/x^2 := by
  induction L generalizing a with
  | nil =>
    simp only [List.map_nil, List.sum_nil, Rat.cast_zero]
    apply integral_nonneg
    intro x
    exact div_nonneg (show (0 : ℝ)≤(phi P x : ℝ) from Int.cast_nonneg ((zudilin_phi_nonneg_periodic P).1 x)) (sq_nonneg x)
  | cons c L ih =>
    simp only [intervalsOrderedCheck, Bool.and_eq_true, decide_eq_true_eq] at hord
    have hal := hord.1.1
    have hlu := hord.1.2
    have hl : 0<c.lower := ha.trans_le hal
    have hu : 0<c.upper := hl.trans_le hlu
    have ha' : (0 : ℝ)<a := by exact_mod_cast ha
    have hl' : (0 : ℝ)<c.lower := by exact_mod_cast hl
    have hal' : (a : ℝ)≤c.lower := by exact_mod_cast hal
    have hlu' : (c.lower : ℝ)≤c.upper := by exact_mod_cast hlu
    have hhead := weighted_interval_lower_ae P c hl' hlu (hc c List.mem_cons_self)
    have htail := ih c.upper hu hord.2
      (fun d hd => hc d (List.mem_cons_of_mem _ hd))
    have hinta := (phi_weighted_integrableOn P).mono_set (Ioi_subset_Ioi ha'.le)
    have hintl := hinta.mono_set (Ioi_subset_Ioi hal')
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hintl hlu'
    have hmono : (∫ x in Ioi (c.lower : ℝ), (phi P x : ℝ)/x^2) ≤
        ∫ x in Ioi (a : ℝ), (phi P x : ℝ)/x^2 := by
      apply setIntegral_mono_set hinta
      · exact Filter.Eventually.of_forall (fun x =>
          div_nonneg (show (0 : ℝ)≤(phi P x : ℝ) from Int.cast_nonneg ((zudilin_phi_nonneg_periodic P).1 x)) (sq_nonneg x))
      · exact Filter.Eventually.of_forall (fun x hx => hal'.trans_lt hx)
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    linarith only [hhead, htail, hsplit, hmono]

end ZudilinZeta
end

-- Component: CertifiedPhiIntegral
section
open MeasureTheory

namespace ZudilinZeta

def PhiCertifiedSegment.shiftInterval (s : PhiCertifiedSegment) (n : ℕ) (cutoff : ℚ) :
    WeightedRationalInterval :=
  ⟨max cutoff (s.lower+n), s.upper+n, s.value⟩

lemma PhiCertifiedSegment.shiftInterval_lower (s : PhiCertifiedSegment) (hs : s.check=true)
    (n : ℕ) (cutoff : ℚ) :
    ∀ᵐ x : ℝ, ((s.shiftInterval n cutoff).lower : ℝ)<x →
      x<((s.shiftInterval n cutoff).upper : ℝ) →
      (s.shiftInterval n cutoff).weight≤phi params13 x := by
  have hp : Function.Periodic (phi params13) 1 := (zudilin_phi_nonneg_periodic params13).2
  have hper (x : ℝ) : phi params13 (x+(n : ℝ))=phi params13 x := by
    simpa only [mul_one] using hp.nat_mul n x
  have hshift := (measurePreserving_sub_right (volume : Measure ℝ) (n : ℝ)).quasiMeasurePreserving.ae
    (s.check_sound hs)
  filter_upwards [hshift] with x hx
  intro hl hu
  have hlo : (s.lower : ℝ)+(n : ℝ)≤((s.shiftInterval n cutoff).lower : ℝ) := by
    have hh : s.lower+(n : ℚ)≤ max cutoff (s.lower+n) := le_max_right _ _
    exact_mod_cast hh
  have hup : ((s.shiftInterval n cutoff).upper : ℝ)=(s.upper : ℝ)+(n : ℝ) := by
    simp only [shiftInterval, Rat.cast_add, Rat.cast_natCast]
  have hb := hx (by linarith only [hlo, hl]) (by linarith only [hup, hu])
  have he := hper (x-(n : ℝ))
  rw [sub_add_cancel] at he
  simpa only [shiftInterval, ← he] using hb

def certifiedPhiIntervals (S : List PhiCertifiedSegment) (cutoff : ℚ) (periods : ℕ) :
    List WeightedRationalInterval :=
  (List.range periods).flatMap (fun (n : ℕ) =>
    (S.filter (fun s => decide (cutoff<s.upper+(n : ℚ)))).map (fun s => s.shiftInterval n cutoff))

lemma certifiedPhiIntervals_lower (S : List PhiCertifiedSegment)
    (hS : S.all PhiCertifiedSegment.check=true) (cutoff : ℚ) (periods : ℕ)
    (c : WeightedRationalInterval) (hc : c∈certifiedPhiIntervals S cutoff periods) :
    ∀ᵐ x : ℝ, (c.lower : ℝ)<x → x<(c.upper : ℝ) → c.weight≤phi params13 x := by
  obtain ⟨n, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  have hs' : s∈S := (List.mem_filter.mp hs).1
  exact s.shiftInterval_lower ((List.all_eq_true.mp hS) s hs') n cutoff

lemma certifiedPhiIntegral_lower (S : List PhiCertifiedSegment)
    (hS : S.all PhiCertifiedSegment.check=true) (cutoff : ℚ) (hcut : 0<cutoff)
    (periods : ℕ)
    (hord : intervalsOrderedCheck cutoff (certifiedPhiIntervals S cutoff periods)=true) :
    ((((certifiedPhiIntervals S cutoff periods).map WeightedRationalInterval.mass).sum : ℚ) : ℝ) ≤
      ∫ x in Set.Ioi (cutoff : ℝ), (phi params13 x : ℝ)/x^2 :=
  weighted_intervals_lower_tail_ae params13 (certifiedPhiIntervals S cutoff periods)
    cutoff hcut hord (certifiedPhiIntervals_lower S hS cutoff periods)

end ZudilinZeta
end

-- Component: C1TailFormula
section
namespace ZudilinZeta

lemma C1_params13_tail_formula :
    C1 params13 = 403-
      ∫ x in Set.Ioi (1/33 : ℝ), (phi params13 x : ℝ)/x^2 := by
  rw [C1, ← zudilin_phi_tail_integral_eq]
  norm_num [params13, eta13, m, Finset.sum_Icc_succ_top]

end ZudilinZeta
end

-- Component: Params13PhiMass
section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ZudilinZeta

lemma rat_sum_floor_scaled_le (L : List ℚ) (D : ℚ) :
    (((L.map (fun q => ⌊D*q⌋)).sum : ℤ) : ℚ) ≤ D*L.sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    exact add_le_add (Int.floor_le _) ih

lemma phiCertifiedIntervals_ordered :
    intervalsOrderedCheck (1/33)
      (certifiedPhiIntervals phiCertifiedSegments (1/33) 4)=true := by
  decide +kernel

lemma phiCertifiedIntervals_floorMass :
    (175500000 : ℤ) <
      ((certifiedPhiIntervals phiCertifiedSegments (1/33) 4).map
        (fun c => ⌊(1000000 : ℚ)*c.mass⌋)).sum := by
  decide +kernel

lemma phiCertifiedIntervals_mass :
    (351/2 : ℚ) <
      ((certifiedPhiIntervals phiCertifiedSegments (1/33) 4).map
        WeightedRationalInterval.mass).sum := by
  have hf := rat_sum_floor_scaled_le
    ((certifiedPhiIntervals phiCertifiedSegments (1/33) 4).map
      WeightedRationalInterval.mass) 1000000
  simp only [List.map_map, Function.comp_def] at hf
  have hh : (175500000 : ℚ) <
      ((((certifiedPhiIntervals phiCertifiedSegments (1/33) 4).map
        (fun c => ⌊(1000000 : ℚ)*c.mass⌋)).sum : ℤ) : ℚ) := by
    exact_mod_cast phiCertifiedIntervals_floorMass
  linarith only [hf, hh]

end ZudilinZeta
end

-- Component: Params13C1Upper
section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace ZudilinZeta

lemma C1_params13_upper_bound : C1 params13<227.5 := by
  have hbound := certifiedPhiIntegral_lower phiCertifiedSegments phiCertifiedSegments_checked
    (1/33) (by norm_num) 4 phiCertifiedIntervals_ordered
  have hmass : (175.5 : ℝ) <
      ((((certifiedPhiIntervals phiCertifiedSegments (1/33) 4).map
        WeightedRationalInterval.mass).sum : ℚ) : ℝ) := by
    rw [show (175.5 : ℝ)=((351/2 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_lt.mpr phiCertifiedIntervals_mass
  rw [C1_params13_tail_formula]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hbound
  linarith only [hbound, hmass]

end ZudilinZeta
end

open ZudilinZeta

theorem solution : C1 params13<227.5 := by
  exact C1_params13_upper_bound
