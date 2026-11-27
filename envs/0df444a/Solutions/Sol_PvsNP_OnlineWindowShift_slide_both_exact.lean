-- Prove2me | solution 1 for PvsNP.OnlineWindowShift.slide_both_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:53:03.044807+00:00
-- url     : https://prove2.me/submissions/4e663289-acbc-45bd-8d6f-493af2feea99

import Definitions.Def_OnlineScratchWindow

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace PvsNP.WorkBoundarySplice

open Function

variable {Q Γ : Type}


/-- An ordinary clocked finite run, allowing an arbitrary final configuration. -/
inductive Steps (M : Machine Q Γ) : Config Q Γ → Config Q Γ → ℕ → Prop
  | refl (a : Config Q Γ) : Steps M a a 0
  | next {a b c : Config Q Γ} {n : ℕ} :
      step M a = some b → Steps M b c n → Steps M a c (n+1)

namespace Steps

theorem append {M : Machine Q Γ} {a b c : Config Q Γ} {n m : ℕ}
    (first : Steps M a b n) (second : Steps M b c m) :
    Steps M a c (n+m) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | next h _ ih => simpa only [Nat.add_right_comm] using .next h (ih second)

theorem iterate {M : Machine Q Γ} {a b : Config Q Γ} {n : ℕ}
    (trace : Steps M a b n) :
    (fun x : Option (Config Q Γ) => x.bind (step M))^[n] (some a) = some b := by
  induction trace with
  | refl => rfl
  | @next a b c n first _ ih =>
    rw [iterate_succ_apply]
    change (fun x : Option (Config Q Γ) => x.bind (step M))^[n] (step M a) = some c
    exact (congrArg (fun x => (fun x : Option (Config Q Γ) => x.bind (step M))^[n] x) first).trans ih

end Steps

end PvsNP.WorkBoundarySplice

namespace PvsNP.OnlineWindowShift

open PvsNP.WorkBoundarySplice

variable {P C : Type}

private theorem before_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ) (before : i < p) :
    frame p w payload i = .blank := by
  have far : i ≠ p+(w : ℤ)+1 := by omega
  simp [frame,ne_of_lt before,far,not_lt_of_ge before.le]

private theorem past_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ)
    (after : p+(w : ℤ)+1 < i) : frame p w payload i = .blank := by
  have near : i ≠ p := by omega
  simp [frame,near,ne_of_gt after,not_lt_of_ge after.le]

theorem near_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) :
    frame p w payload p = .near := by simp [frame]

private theorem far_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) :
    frame p w payload (p+(w : ℤ)+1) = .far := by
  have distinct : p+(w : ℤ)+1 ≠ p := by omega
  simp [frame,distinct]

theorem inside_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ)
    (near : p < i) (far : i < p+(w : ℤ)+1) :
    frame p w payload i = .data (payload (i-p-1).toNat) := by
  simp [frame,ne_of_gt near,ne_of_lt far,near,far]

private theorem translate_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ) :
    frame (p+1) w payload i = frame p w payload (i-1) := by
  have near : i = p+1 ↔ i-1 = p := by omega
  have far : i = p+1+(w : ℤ)+1 ↔ i-1 = p+(w : ℤ)+1 := by omega
  have inside : (p+1 < i ∧ i < p+1+(w : ℤ)+1) ↔ (p < i-1 ∧ i-1 < p+(w : ℤ)+1) := by omega
  have index : i-(p+1)-1 = i-1-p-1 := by omega
  simp only [frame,near,far,inside,index]

private def blend (p : ℤ) (old new : ℤ → Cell P) : ℤ → Cell P :=
  fun i => if i < p then new i else old i

private theorem blend_before (p : ℤ) (w : ℕ) (payload : ℕ → P) :
    blend p (frame p w payload) (frame (p+1) w payload) = frame p w payload := by
  funext i
  by_cases before : i < p
  · simp only [blend,if_pos before]
    rw [before_frame _ _ _ _ (by omega),before_frame _ _ _ _ before]
  · exact if_neg before

private theorem blend_after (p : ℤ) (w : ℕ) (payload : ℕ → P) :
    blend (p+(w : ℤ)+3) (frame p w payload) (frame (p+1) w payload) =
      frame (p+1) w payload := by
  funext i
  by_cases before : i < p+(w : ℤ)+3
  · exact if_pos before
  · simp only [blend,if_neg before]
    rw [past_frame _ _ _ _ (by omega),past_frame _ _ _ _ (by omega)]

private theorem blend_write (p : ℤ) (old new : ℤ → Cell P) :
    write (blend p old new) p (new p) = blend (p+1) old new := by
  funext i
  by_cases here : i = p
  · subst i
    simp [write,blend]
  · have range : i < p ↔ i < p+1 := by omega
    simp [write,blend,here,range]

private theorem write_same (t : ℤ → Cell P) (p : ℤ) : write t p (t p) = t := by
  funext i
  by_cases same : i = p
  · subst i
    simp [write]
  · simp [write,same]

private theorem action (consumer : ℤ → C) (scratch after : ℤ → Cell P)
    (p q : ℤ) (mode next : Phase P) (symbol : Cell P) (d : Motion)
    (read : command mode (scratch p) = some (next,symbol,d))
    (head : d.shift p = q) (code : write scratch p symbol = after) :
    step shiftRightMachine ⟨mode,p,tracks consumer scratch⟩ =
      some ⟨next,q,tracks consumer after⟩ := by
  unfold step shiftRightMachine
  change ((command mode (scratch p)).map _).map _ = _
  rw [read]
  simp only [Option.map_some,head,Option.some.injEq]
  congr 1
  rw [← code]
  funext i
  by_cases atHead : i = p
  · subst i
    simp [write,tracks]
  · simp [write,tracks,atHead]

private def carryAt (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) (i : ℕ) :
    Config (Phase P) (C × Cell P) :=
  ⟨.carry (frame p w payload (p+(i : ℤ)-1)),p+(i : ℤ),
    tracks consumer (blend (p+(i : ℤ)) (frame p w payload) (frame (p+1) w payload))⟩

private def depositAt (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    Config (Phase P) (C × Cell P) :=
  ⟨.deposit,p+(w : ℤ)+2,
    tracks consumer (blend (p+(w : ℤ)+2) (frame p w payload) (frame (p+1) w payload))⟩

private theorem begin_shift (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    step shiftRightMachine ⟨.enter,p,tracks consumer (frame p w payload)⟩ =
      some (carryAt p w payload consumer 1) := by
  have writeBlank : frame (p+1) w payload p = .blank := before_frame _ _ _ _ (by omega)
  have initial : write (frame p w payload) p .blank =
      blend (p+1) (frame p w payload) (frame (p+1) w payload) := by
    have update := blend_write p (frame p w payload) (frame (p+1) w payload)
    rw [blend_before p w payload,writeBlank] at update
    exact update
  have source := action consumer (frame p w payload) _ p (p+1) .enter (.carry .near) .blank .right
    (by rw [near_frame]; rfl) rfl initial
  simpa [carryAt,near_frame] using source

private theorem run_carry (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C)
    (rem i : ℕ) (positive : 0 < i) (fit : i+rem = w+1) :
    Steps shiftRightMachine (carryAt p w payload consumer i) (depositAt p w payload consumer) (rem+1) := by
  induction rem generalizing i with
  | zero =>
    have far : p+(i : ℤ) = p+(w : ℤ)+1 := by omega
    have next : p+(i : ℤ)+1 = p+(w : ℤ)+2 := by omega
    have read : blend (p+(i : ℤ)) (frame p w payload) (frame (p+1) w payload) (p+(i : ℤ)) =
        .far := by simp only [blend,lt_irrefl,if_false,far,far_frame]
    have code := blend_write (p+(i : ℤ)) (frame p w payload) (frame (p+1) w payload)
    rw [translate_frame,next] at code
    have last := action consumer _ _ (p+(i : ℤ)) (p+(w : ℤ)+2)
      (.carry (frame p w payload (p+(i : ℤ)-1))) .deposit (frame p w payload (p+(i : ℤ)-1))
      .right (by rw [read]; rfl) next code
    exact .next last (.refl _)
  | succ rem ih =>
    have read : blend (p+(i : ℤ)) (frame p w payload) (frame (p+1) w payload) (p+(i : ℤ)) =
        .data (payload ((p+(i : ℤ)-p-1).toNat)) := by
      simp only [blend,lt_irrefl,if_false]
      exact inside_frame _ _ _ _ (by omega) (by omega)
    have next : p+(i : ℤ)+1 = p+((i+1 : ℕ) : ℤ) := by omega
    have carried : frame p w payload (p+((i+1 : ℕ) : ℤ)-1) =
        .data (payload ((p+(i : ℤ)-p-1).toNat)) := by
      rw [← next,Int.add_sub_cancel]
      exact inside_frame _ _ _ _ (by omega) (by omega)
    have code := blend_write (p+(i : ℤ)) (frame p w payload) (frame (p+1) w payload)
    rw [translate_frame,next] at code
    have now := action consumer _ _ (p+(i : ℤ)) (p+((i+1 : ℕ) : ℤ))
      (.carry (frame p w payload (p+(i : ℤ)-1)))
      (.carry (frame p w payload (p+((i+1 : ℕ) : ℤ)-1))) (frame p w payload (p+(i : ℤ)-1))
      .right (by rw [read,carried]; rfl) next code
    exact .next now (ih (i+1) (by omega) (by omega))

private theorem deposit_shift (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    step shiftRightMachine (depositAt p w payload consumer) =
      some ⟨.returnHome,p+1+(w : ℤ),tracks consumer (frame (p+1) w payload)⟩ := by
  have read : blend (p+(w : ℤ)+2) (frame p w payload) (frame (p+1) w payload) (p+(w : ℤ)+2) =
      .blank := by
    simp only [blend,lt_irrefl,if_false]
    exact past_frame _ _ _ _ (by omega)
  have far : frame (p+1) w payload (p+(w : ℤ)+2) = .far := by
    rw [show p+(w : ℤ)+2 = p+1+(w : ℤ)+1 by omega]
    exact far_frame _ _ _
  have code := blend_write (p+(w : ℤ)+2) (frame p w payload) (frame (p+1) w payload)
  rw [far,show p+(w : ℤ)+2+1 = p+(w : ℤ)+3 by omega,blend_after] at code
  exact action consumer _ _ _ _ .deposit .returnHome .far .left (by rw [read]; rfl)
    (by simp only [Motion.shift]; omega) code

theorem seek_near_from_offset (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C)
    (i : ℕ) (within : i ≤ w) :
    Steps shiftRightMachine
      ⟨.returnHome,p+(i : ℤ),tracks consumer (frame p w payload)⟩
      ⟨.done,p,tracks consumer (frame p w payload)⟩ (i+1) := by
  induction i with
  | zero =>
    have head : p+(0 : ℤ) = p := by omega
    simp only [Nat.cast_zero,add_zero]
    have read := near_frame p w payload
    refine .next (action consumer _ _ p p .returnHome .done .near .stay (by rw [read]; rfl) rfl ?_) (.refl _)
    rw [← read]
    exact write_same _ _
  | succ i ih =>
    let pos := p+((i+1 : ℕ) : ℤ)
    have read := inside_frame p w payload pos (by dsimp [pos]; omega) (by dsimp [pos]; omega)
    refine .next (action consumer _ _ pos (p+(i : ℤ)) .returnHome .returnHome
      (frame p w payload pos) .left (by rw [read]; rfl) (by dsimp [pos,Motion.shift]; omega)
      (write_same _ _)) (ih (by omega))

/-- A read-only scan from the far marker reaches the near marker. -/
theorem seek_near_from_far (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    Steps shiftRightMachine ⟨.returnHome,p+(w : ℤ)+1,tracks consumer (frame p w payload)⟩
      ⟨.done,p,tracks consumer (frame p w payload)⟩ (w+2) := by
  have read := far_frame p w payload
  refine .next (action consumer _ _ _ (p+(w : ℤ)) .returnHome .returnHome .far .left
    (by rw [read]; rfl) (by simp [Motion.shift]) ?_) (seek_near_from_offset p w payload consumer w le_rfl)
  rw [← read]
  exact write_same _ _

/-- A fixed finite local program shifts the full scratch window one cell to
the right, returns to the new near marker, and preserves every consumer
cell. Its clock is exact, including marker handling and the return scan. -/
theorem shift_right_exact (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    Steps shiftRightMachine ⟨.enter,p,tracks consumer (frame p w payload)⟩
      ⟨.done,p+1,tracks consumer (frame (p+1) w payload)⟩ (2*w+4) := by
  have run := run_carry p w payload consumer w 1 (by omega) (by omega)
  have back := seek_near_from_offset (p+1) w payload consumer w le_rfl
  have exactRun := Steps.next (begin_shift p w payload consumer)
    (run.append (Steps.next (deposit_shift p w payload consumer) back))
  rwa [show w+1+(w+1+1)+1 = 2*w+4 by omega] at exactRun

private theorem flipPos_twice (mirror : Bool) (z : ℤ) :
    flipPos mirror (flipPos mirror z) = z := by
  cases mirror <;> simp [flipPos]

private theorem flipSquare_twice (mirror : Bool) (cell : C × Cell P) :
    flipSquare mirror (flipSquare mirror cell) = cell := by
  rcases cell with ⟨main,cell⟩
  cases mirror <;> cases cell <;> rfl

private theorem flipMotion_shift (mirror : Bool) (motion : Motion) (z : ℤ) :
    (flipMotion mirror motion).shift (flipPos mirror z) = flipPos mirror (motion.shift z) := by
  cases mirror <;> cases motion <;> simp [flipMotion,flipPos,Motion.shift] <;> omega

/-- A fixed local machine. Reflected phases swap the two scratch markers
and reverse the source head motion. The consumer symbol is unchanged. -/
private def liftConfig (pass : LeftPass) (cfg : Config (Phase P) (C × Cell P)) :
    Config (LeftPhase P) (C × Cell P) :=
  ⟨leftPhase pass cfg.state,flipPos pass.mirrored cfg.head,
    fun z => flipSquare pass.mirrored (cfg.tape (flipPos pass.mirrored z))⟩

private theorem lift_step (pass : LeftPass) (a b : Config (Phase P) (C × Cell P))
    (ran : step shiftRightMachine a = some b) :
    step shiftLeftMachine (liftConfig pass a) = some (liftConfig pass b) := by
  rcases a with ⟨mode,pos,tape⟩
  have active : leftPhase pass mode = .active pass mode := by
    cases mode with
    | done =>
      change none = some b at ran
      contradiction
    | _ => rfl
  unfold step at ran
  cases src : shiftRightMachine mode (tape pos) with
  | none => simp only [src,Option.map_none,reduceCtorEq] at ran
  | some action =>
    rcases action with ⟨next,out,motion⟩
    simp only [src,Option.map_some,Option.some.injEq] at ran
    subst b
    have cmd : shiftLeftMachine (leftPhase pass mode)
        (flipSquare pass.mirrored (tape (flipPos pass.mirrored (flipPos pass.mirrored pos)))) =
        some (leftPhase pass next,flipSquare pass.mirrored out,flipMotion pass.mirrored motion) := by
      rw [active,shiftLeftMachine,flipPos_twice,flipSquare_twice,src]
      rfl
    unfold step liftConfig
    dsimp only
    rw [cmd]
    simp only [Option.map_some,Option.some.injEq,flipMotion_shift]
    congr 1
    funext i
    by_cases hit : i = flipPos pass.mirrored pos
    · subst i
      simp [write,flipPos_twice]
    · have miss : flipPos pass.mirrored i ≠ pos := by
        intro he
        apply hit
        rw [← he,flipPos_twice]
      simp [write,hit,miss]

private theorem lift_steps (pass : LeftPass) {a b : Config (Phase P) (C × Cell P)}
    {n : ℕ} (ran : Steps shiftRightMachine a b n) :
    Steps shiftLeftMachine (liftConfig pass a) (liftConfig pass b) n := by
  induction ran with
  | refl a => exact .refl _
  | next stepAB _ ih => exact .next (lift_step pass _ _ stepAB) ih

private def mirrorAnchor (p : ℤ) (w : ℕ) : ℤ :=
  -(p+(w : ℤ)+1)

private def reversePayload (w : ℕ) (payload : ℕ → P) (i : ℕ) : P :=
  payload (w-1-i)

private theorem flip_frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ) :
    flipCell true (frame (mirrorAnchor p w) w (reversePayload w payload) (-i)) =
      frame p w payload i := by
  have reflectedNear : -i = mirrorAnchor p w ↔ i = p+(w : ℤ)+1 := by
    unfold mirrorAnchor
    omega
  have reflectedFar : -i = mirrorAnchor p w+(w : ℤ)+1 ↔ i = p := by
    unfold mirrorAnchor
    omega
  have reflectedInside : (mirrorAnchor p w < -i ∧ -i < mirrorAnchor p w+(w : ℤ)+1) ↔
      (p < i ∧ i < p+(w : ℤ)+1) := by
    unfold mirrorAnchor
    omega
  simp only [frame,reflectedNear,reflectedFar,reflectedInside]
  by_cases first : i = p
  · have last : i ≠ p+(w : ℤ)+1 := by omega
    simp only [if_neg last,if_pos first,flipCell,if_true]
  · by_cases last : i = p+(w : ℤ)+1
    · simp only [if_pos last,if_neg first,flipCell,if_true]
    · by_cases inside : p < i ∧ i < p+(w : ℤ)+1
      · have index : w-1-(-i-mirrorAnchor p w-1).toNat = (i-p-1).toNat := by
          unfold mirrorAnchor
          omega
        simp only [if_neg first,if_neg last,if_pos inside,flipCell,if_true,reversePayload,index]
      · simp only [if_neg first,if_neg last,if_neg inside,flipCell,if_true]

private theorem lift_mirror_track (pass : LeftPass) (reflected : pass.mirrored = true)
    (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) (mode : Phase P) (h : ℤ) :
    liftConfig pass ⟨mode,h,
      tracks (fun i => consumer (-i)) (frame (mirrorAnchor p w) w (reversePayload w payload))⟩ =
      ⟨leftPhase pass mode,-h,tracks consumer (frame p w payload)⟩ := by
  unfold liftConfig
  dsimp only
  rw [reflected]
  simp only [flipPos,if_true]
  congr 1
  funext i
  change (consumer (- -i),flipCell true (frame (mirrorAnchor p w) w (reversePayload w payload) (-i))) =
    (consumer i,frame p w payload i)
  rw [neg_neg,flip_frame]

private theorem lift_normal_track (pass : LeftPass) (normal : pass.mirrored = false)
    (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) (mode : Phase P) (h : ℤ) :
    liftConfig pass ⟨mode,h,tracks consumer (frame p w payload)⟩ =
      ⟨leftPhase pass mode,h,tracks consumer (frame p w payload)⟩ := by
  unfold liftConfig
  dsimp only
  rw [normal]
  rfl

/-- This finite program shifts the complete scratch frame left by one cell,
leaves every consumer cell untouched, and finishes at the relocated near
marker. It needs two full searches and the reflected shift between them. -/
theorem shift_left_exact (p : ℤ) (w : ℕ) (payload : ℕ → P) (consumer : ℤ → C) :
    Steps shiftLeftMachine
      ⟨.active .seekFar .returnHome,p,tracks consumer (frame p w payload)⟩
      ⟨.done,p-1,tracks consumer (frame (p-1) w payload)⟩ (4*w+8) := by
  have h1 := lift_steps (pass := .seekFar) (seek_near_from_far (mirrorAnchor p w) w
    (reversePayload w payload) (fun i => consumer (-i)))
  rw [lift_mirror_track .seekFar rfl,lift_mirror_track .seekFar rfl] at h1
  have outward : Steps shiftLeftMachine
      ⟨.active .seekFar .returnHome,p,tracks consumer (frame p w payload)⟩
      ⟨.active .shift .enter,p+(w : ℤ)+1,tracks consumer (frame p w payload)⟩ (w+2) := by
    simpa only [leftPhase,mirrorAnchor,neg_neg,show -(-(p+(w : ℤ)+1)+(w : ℤ)+1) = p by omega] using h1
  have h2 := lift_steps (pass := .shift) (shift_right_exact (mirrorAnchor p w) w
    (reversePayload w payload) (fun i => consumer (-i)))
  have anchor : mirrorAnchor p w+1 = mirrorAnchor (p-1) w := by
    unfold mirrorAnchor
    omega
  rw [lift_mirror_track .shift rfl,anchor,lift_mirror_track .shift rfl] at h2
  have moved : Steps shiftLeftMachine
      ⟨.active .shift .enter,p+(w : ℤ)+1,tracks consumer (frame p w payload)⟩
      ⟨.active .seekNear .returnHome,p-1+(w : ℤ)+1,tracks consumer (frame (p-1) w payload)⟩
      (2*w+4) := by
    simpa only [leftPhase,mirrorAnchor,neg_neg] using h2
  have h3 := lift_steps (pass := .seekNear) (seek_near_from_far (p-1) w payload consumer)
  rw [lift_normal_track .seekNear rfl,lift_normal_track .seekNear rfl] at h3
  have back : Steps shiftLeftMachine
      ⟨.active .seekNear .returnHome,p-1+(w : ℤ)+1,tracks consumer (frame (p-1) w payload)⟩
      ⟨.done,p-1,tracks consumer (frame (p-1) w payload)⟩ (w+2) := h3
  have all := outward.append (moved.append back)
  rwa [show (w+2)+(2*w+4+(w+2)) = 4*w+8 by omega] at all

end PvsNP.OnlineWindowShift

open Function PvsNP.WorkBoundarySplice PvsNP.OnlineWindowShift

variable {P C : Type}

theorem solution (p : ℤ) (w : ℕ)
    (payload : ℕ → P) (consumer : ℤ → C) :
    ((fun z : Option (Config (Phase P) (C × Cell P)) => z.bind (step shiftRightMachine))^[2*w+4])
      (some ⟨.enter,p,tracks consumer (frame p w payload)⟩) =
        some ⟨.done,p+1,tracks consumer (frame (p+1) w payload)⟩ ∧
    ((fun z : Option (Config (LeftPhase P) (C × Cell P)) => z.bind (step shiftLeftMachine))^[4*w+8])
      (some ⟨.active .seekFar .returnHome,p,tracks consumer (frame p w payload)⟩) =
        some ⟨.done,p-1,tracks consumer (frame (p-1) w payload)⟩ := by
  exact ⟨(shift_right_exact p w payload consumer).iterate,
    (shift_left_exact p w payload consumer).iterate⟩

#print axioms solution
