-- Prove2me | solution 1 for PvsNP.isPolyTime_comp
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T07:20:21.993625+00:00
-- url     : https://prove2.me/submissions/8b9e413d-107f-462f-bfa0-5e255ca4b7e2

import Definitions.Def_PvsNP_complexity_classes

open Computability Turing PvsNP

namespace CompTM

variable (A B : FinTM2)

/-- Stack indices of the composed machine: the stacks of `A`, the stacks of `B`, and one
auxiliary stack used to transfer `A`'s output to `B`'s input. -/
abbrev CK : Type := A.K ⊕ B.K ⊕ Unit

instance : DecidableEq (CK A B) := inferInstanceAs (DecidableEq (A.K ⊕ B.K ⊕ Unit))
instance : Fintype (CK A B) := by
  haveI := A.kFin; haveI := B.kFin
  exact inferInstanceAs (Fintype (A.K ⊕ B.K ⊕ Unit))

/-- Stack alphabets of the composed machine. -/
@[reducible] def CGam : CK A B → Type
  | .inl a => A.Γ a
  | .inr (.inl b) => B.Γ b
  | .inr (.inr _) => Bool

/-- Stack contents of the composed machine, assembled from `A`'s stacks, `B`'s stacks and the
auxiliary stack. -/
@[reducible] def cstk (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux : List Bool) :
    ∀ k : CK A B, List (CGam A B k)
  | .inl a => SA a
  | .inr (.inl b) => SB b
  | .inr (.inr _) => aux

variable {A B}

theorem cstk_update_inl (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux : List Bool)
    (k : A.K) (l : List (A.Γ k)) :
    Function.update (cstk A B SA SB aux) (Sum.inl k) l
      = cstk A B (Function.update SA k l) SB aux := by
  funext k'
  match k' with
  | .inl k'' =>
      by_cases h : k'' = k
      · subst h
        exact (Function.update_self (Sum.inl k'' : CK A B) l (cstk A B SA SB aux)).trans
          (Function.update_self k'' l SA).symm
      · have h' : (Sum.inl k'' : CK A B) ≠ Sum.inl k := by simpa using h
        exact (Function.update_of_ne h' l (cstk A B SA SB aux)).trans
          (Function.update_of_ne h l SA).symm
  | .inr (.inl b) =>
      have h' : (Sum.inr (Sum.inl b) : CK A B) ≠ Sum.inl k := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)
  | .inr (.inr u) =>
      have h' : (Sum.inr (Sum.inr u) : CK A B) ≠ Sum.inl k := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)

theorem cstk_update_inrl (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux : List Bool)
    (k : B.K) (l : List (B.Γ k)) :
    Function.update (cstk A B SA SB aux) (Sum.inr (Sum.inl k)) l
      = cstk A B SA (Function.update SB k l) aux := by
  funext k'
  match k' with
  | .inl a =>
      have h' : (Sum.inl a : CK A B) ≠ Sum.inr (Sum.inl k) := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)
  | .inr (.inl k'') =>
      by_cases h : k'' = k
      · subst h
        exact (Function.update_self (Sum.inr (Sum.inl k'') : CK A B) l
          (cstk A B SA SB aux)).trans (Function.update_self k'' l SB).symm
      · have h' : (Sum.inr (Sum.inl k'') : CK A B) ≠ Sum.inr (Sum.inl k) := by simpa using h
        exact (Function.update_of_ne h' l (cstk A B SA SB aux)).trans
          (Function.update_of_ne h l SB).symm
  | .inr (.inr u) =>
      have h' : (Sum.inr (Sum.inr u) : CK A B) ≠ Sum.inr (Sum.inl k) := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)

theorem cstk_update_aux (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux l : List Bool) :
    Function.update (cstk A B SA SB aux) (Sum.inr (Sum.inr ())) l = cstk A B SA SB l := by
  funext k'
  match k' with
  | .inl a =>
      have h' : (Sum.inl a : CK A B) ≠ Sum.inr (Sum.inr ()) := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)
  | .inr (.inl b) =>
      have h' : (Sum.inr (Sum.inl b) : CK A B) ≠ Sum.inr (Sum.inr ()) := by simp
      exact Function.update_of_ne h' l (cstk A B SA SB aux)
  | .inr (.inr u) =>
      exact Function.update_self (Sum.inr (Sum.inr ()) : CK A B) l (cstk A B SA SB aux)


variable (A B)

/-- The internal state of the composed machine. -/
abbrev CSig : Type := A.σ × B.σ × Option Bool

/-- The labels of the two transfer loops. -/
inductive Xfer where
  | toAux : Xfer
  | toIn : Xfer
  deriving DecidableEq, Inhabited

instance : Fintype Xfer := ⟨{Xfer.toAux, Xfer.toIn}, by intro x; cases x <;> simp⟩

/-- The labels of the composed machine: those of `A`, those of `B`, and two labels for the
two transfer loops. -/
abbrev CLbl : Type := A.Λ ⊕ B.Λ ⊕ Xfer

instance : Fintype (CLbl A B) := by
  haveI := A.ΛFin; haveI := B.ΛFin
  exact inferInstanceAs (Fintype (A.Λ ⊕ B.Λ ⊕ Xfer))

instance : Fintype (CSig A B) := by
  haveI := A.σFin; haveI := B.σFin
  exact inferInstanceAs (Fintype (A.σ × B.σ × Option Bool))

/-- Lift a statement of `A` to the composed machine. Halting of `A` becomes a jump to the
first transfer loop. -/
def liftA : TM2.Stmt A.Γ A.Λ A.σ → TM2.Stmt (CGam A B) (CLbl A B) (CSig A B)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (liftA q)
  | .peek k f q => .peek (Sum.inl k) (fun v x => (f v.1 x, v.2)) (liftA q)
  | .pop k f q => .pop (Sum.inl k) (fun v x => (f v.1 x, v.2)) (liftA q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftA q)
  | .branch c q₁ q₂ => .branch (fun v => c v.1) (liftA q₁) (liftA q₂)
  | .goto l => .goto (fun v => Sum.inl (l v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr Xfer.toAux))

/-- Lift a statement of `B` to the composed machine. -/
def liftB : TM2.Stmt B.Γ B.Λ B.σ → TM2.Stmt (CGam A B) (CLbl A B) (CSig A B)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (liftB q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v x => (v.1, f v.2.1 x, v.2.2)) (liftB q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v x => (v.1, f v.2.1 x, v.2.2)) (liftB q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftB q)
  | .branch c q₁ q₂ => .branch (fun v => c v.2.1) (liftB q₁) (liftB q₂)
  | .goto l => .goto (fun v => Sum.inr (Sum.inl (l v.2.1)))
  | .halt => .halt

/-- Labels of `A`, transported to the composed machine; halting becomes the transfer loop. -/
def labA : Option A.Λ → Option (CLbl A B)
  | none => some (Sum.inr (Sum.inr Xfer.toAux))
  | some l => some (Sum.inl l)

/-- Labels of `B`, transported to the composed machine. -/
def labB : Option B.Λ → Option (CLbl A B)
  | none => none
  | some l => some (Sum.inr (Sum.inl l))

/-- A configuration of `A`, transported to the composed machine. -/
def cfgA (c : TM2.Cfg A.Γ A.Λ A.σ) (vB : B.σ) (o : Option Bool)
    (SB : ∀ k, List (B.Γ k)) (aux : List Bool) :
    TM2.Cfg (CGam A B) (CLbl A B) (CSig A B) :=
  ⟨labA A B c.l, (c.var, vB, o), cstk A B c.stk SB aux⟩

/-- A configuration of `B`, transported to the composed machine. -/
def cfgB (c : TM2.Cfg B.Γ B.Λ B.σ) (vA : A.σ) (o : Option Bool)
    (SA : ∀ k, List (A.Γ k)) (aux : List Bool) :
    TM2.Cfg (CGam A B) (CLbl A B) (CSig A B) :=
  ⟨labB A B c.l, (vA, c.var, o), cstk A B SA c.stk aux⟩

variable {A B}

theorem stepAux_liftA (q : TM2.Stmt A.Γ A.Λ A.σ) (vA : A.σ) (vB : B.σ) (o : Option Bool)
    (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux : List Bool) :
    TM2.stepAux (liftA A B q) (vA, vB, o) (cstk A B SA SB aux)
      = cfgA A B (TM2.stepAux q vA SA) vB o SB aux := by
  induction q generalizing vA SA with
  | push k f q ih =>
      simp only [liftA, TM2.stepAux]
      erw [cstk_update_inl]
      exact ih _ _
  | peek k f q ih => simp only [liftA, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
      simp only [liftA, TM2.stepAux]
      erw [cstk_update_inl]
      exact ih _ _
  | load a q ih => simp only [liftA, TM2.stepAux]; exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ =>
      simp only [liftA, TM2.stepAux]
      cases hc : c vA
      · simpa [hc] using ih₂ vA SA
      · simpa [hc] using ih₁ vA SA
  | goto l => rfl
  | halt => rfl

theorem stepAux_liftB (q : TM2.Stmt B.Γ B.Λ B.σ) (vA : A.σ) (vB : B.σ) (o : Option Bool)
    (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k)) (aux : List Bool) :
    TM2.stepAux (liftB A B q) (vA, vB, o) (cstk A B SA SB aux)
      = cfgB A B (TM2.stepAux q vB SB) vA o SA aux := by
  induction q generalizing vB SB with
  | push k f q ih =>
      simp only [liftB, TM2.stepAux]
      erw [cstk_update_inrl]
      exact ih _ _
  | peek k f q ih => simp only [liftB, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
      simp only [liftB, TM2.stepAux]
      erw [cstk_update_inrl]
      exact ih _ _
  | load a q ih => simp only [liftB, TM2.stepAux]; exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ =>
      simp only [liftB, TM2.stepAux]
      cases hc : c vB
      · simpa [hc] using ih₂ vB SB
      · simpa [hc] using ih₁ vB SB
  | goto l => rfl
  | halt => rfl


variable (A B)

/-- The program of the composed machine. -/
def cprog (oA : A.Γ A.k₁ ≃ Bool) (iB : B.Γ B.k₀ ≃ Bool) :
    CLbl A B → TM2.Stmt (CGam A B) (CLbl A B) (CSig A B)
  | .inl la => liftA A B (A.m la)
  | .inr (.inl lb) => liftB A B (B.m lb)
  | .inr (.inr .toAux) =>
      .pop (Sum.inl A.k₁) (fun _ x => (A.initialState, B.initialState, x.map oA)) <|
        .branch (fun v => v.2.2.isSome)
          (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
            .goto fun _ => Sum.inr (Sum.inr Xfer.toAux))
          (.goto fun _ => Sum.inr (Sum.inr Xfer.toIn))
  | .inr (.inr .toIn) =>
      .pop (Sum.inr (Sum.inr ())) (fun _ x => (A.initialState, B.initialState, x)) <|
        .branch (fun v => v.2.2.isSome)
          (.push (Sum.inr (Sum.inl B.k₀)) (fun v => iB.symm (v.2.2.getD false)) <|
            .goto fun _ => Sum.inr (Sum.inr Xfer.toIn))
          (.goto fun _ => Sum.inr (Sum.inl B.main))

/-- The composed machine: it runs `A`, transfers `A`'s output to `B`'s input, and runs `B`. -/
@[reducible] def cmach (oA : A.Γ A.k₁ ≃ Bool) (iB : B.Γ B.k₀ ≃ Bool) : FinTM2 where
  K := CK A B
  k₀ := Sum.inl A.k₀
  k₁ := Sum.inr (Sum.inl B.k₁)
  Γ := CGam A B
  Λ := CLbl A B
  main := Sum.inl A.main
  σ := CSig A B
  initialState := (A.initialState, B.initialState, none)
  Γk₀Fin := A.Γk₀Fin
  m := cprog A B oA iB

variable {A B}

theorem iterate_none {σ : Type*} (f : σ → Option σ) (k : ℕ) :
    (flip bind f)^[k] none = none := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, show (flip bind f) none = none from rfl]
      exact ih

variable (oA : A.Γ A.k₁ ≃ Bool) (iB : B.Γ B.k₀ ≃ Bool)

/-- Steps of `A` are simulated step by step by the composed machine. -/
theorem iter_liftA (k : ℕ) (c c' : TM2.Cfg A.Γ A.Λ A.σ)
    (vB : B.σ) (o : Option Bool) (SB : ∀ k, List (B.Γ k)) (aux : List Bool)
    (h : (flip bind (TM2.step A.m))^[k] (some c) = some c') :
    (flip bind (cmach A B oA iB).step)^[k] (some (cfgA A B c vB o SB aux))
      = some (cfgA A B c' vB o SB aux) := by
  induction k generalizing c with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at h ⊢
      obtain rfl := Option.some_inj.mp h
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h ⊢
      obtain ⟨l, v, S⟩ := c
      match l with
      | none =>
          exfalso
          rw [show (flip bind (TM2.step A.m)) (some ⟨none, v, S⟩) = none from rfl,
            iterate_none (TM2.step A.m) n] at h
          exact absurd h (by simp)
      | some l =>
          have hstep : (flip bind (cmach A B oA iB).step) (some (cfgA A B ⟨some l, v, S⟩ vB o SB aux))
              = some (cfgA A B (TM2.stepAux (A.m l) v S) vB o SB aux) := by
            show some (TM2.stepAux (cprog A B oA iB (Sum.inl l)) (v, vB, o) (cstk A B S SB aux)) = _
            rw [show cprog A B oA iB (Sum.inl l) = liftA A B (A.m l) from rfl, stepAux_liftA]
          rw [hstep]
          exact ih _ h

/-- Steps of `B` are simulated step by step by the composed machine. -/
theorem iter_liftB (k : ℕ) (c c' : TM2.Cfg B.Γ B.Λ B.σ)
    (vA : A.σ) (o : Option Bool) (SA : ∀ k, List (A.Γ k)) (aux : List Bool)
    (h : (flip bind (TM2.step B.m))^[k] (some c) = some c') :
    (flip bind (cmach A B oA iB).step)^[k] (some (cfgB A B c vA o SA aux))
      = some (cfgB A B c' vA o SA aux) := by
  induction k generalizing c with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at h ⊢
      obtain rfl := Option.some_inj.mp h
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h ⊢
      obtain ⟨l, v, S⟩ := c
      match l with
      | none =>
          exfalso
          rw [show (flip bind (TM2.step B.m)) (some ⟨none, v, S⟩) = none from rfl,
            iterate_none (TM2.step B.m) n] at h
          exact absurd h (by simp)
      | some l =>
          have hstep : (flip bind (cmach A B oA iB).step) (some (cfgB A B ⟨some l, v, S⟩ vA o SA aux))
              = some (cfgB A B (TM2.stepAux (B.m l) v S) vA o SA aux) := by
            show some (TM2.stepAux (cprog A B oA iB (Sum.inr (Sum.inl l))) (vA, v, o)
              (cstk A B SA S aux)) = _
            rw [show cprog A B oA iB (Sum.inr (Sum.inl l)) = liftB A B (B.m l) from rfl,
              stepAux_liftB]
          rw [hstep]
          exact ih _ h


/-- The first transfer loop: `A`'s output stack is moved, reversed, onto the auxiliary stack. -/
theorem toAux_iter (x : List (A.Γ A.k₁)) (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k))
    (aux : List Bool) (v : CSig A B) :
    (flip bind (cmach A B oA iB).step)^[x.length + 1]
        (some ⟨some (Sum.inr (Sum.inr Xfer.toAux)), v,
          cstk A B (Function.update SA A.k₁ x) SB aux⟩)
      = some ⟨some (Sum.inr (Sum.inr Xfer.toIn)), (A.initialState, B.initialState, none),
          cstk A B (Function.update SA A.k₁ []) SB ((x.map oA).reverse ++ aux)⟩ := by
  induction x generalizing aux v with
  | nil =>
      show (flip bind (cmach A B oA iB).step) _ = _
      show some (TM2.stepAux (cprog A B oA iB (Sum.inr (Sum.inr Xfer.toAux))) v
        (cstk A B (Function.update SA A.k₁ []) SB aux)) = _
      have hproj : cstk A B (Function.update SA A.k₁ ([] : List (A.Γ A.k₁))) SB aux
          (Sum.inl A.k₁) = [] := by simp
      simp only [cprog, TM2.stepAux, hproj, List.head?_nil, Option.map_none,
        Option.isSome_none, cond_false, List.tail_nil, List.map_nil, List.reverse_nil,
        List.nil_append]
      erw [cstk_update_inl]
      simp only [Function.update_idem]
      rfl
  | cons b t ih =>
      rw [show (b :: t).length + 1 = (t.length + 1) + 1 by simp, Function.iterate_succ_apply]
      have hstep : (flip bind (cmach A B oA iB).step)
            (some ⟨some (Sum.inr (Sum.inr Xfer.toAux)), v,
              cstk A B (Function.update SA A.k₁ (b :: t)) SB aux⟩)
          = some ⟨some (Sum.inr (Sum.inr Xfer.toAux)),
              (A.initialState, B.initialState, some (oA b)),
              cstk A B (Function.update SA A.k₁ t) SB (oA b :: aux)⟩ := by
        show some (TM2.stepAux (cprog A B oA iB (Sum.inr (Sum.inr Xfer.toAux))) v
          (cstk A B (Function.update SA A.k₁ (b :: t)) SB aux)) = _
        have hproj : cstk A B (Function.update SA A.k₁ (b :: t)) SB aux (Sum.inl A.k₁)
            = b :: t := by simp
        simp only [cprog, TM2.stepAux, hproj, List.head?_cons, List.tail_cons,
          Option.map_some, Option.isSome_some, cond_true, Option.getD_some]
        erw [cstk_update_inl]
        rw [show cstk A B (Function.update SA A.k₁ t) SB aux (Sum.inr (Sum.inr ())) = aux from rfl]
        erw [cstk_update_aux]
        simp only [Function.update_idem]
        rfl
      rw [hstep, ih (oA b :: aux) _]
      simp

/-- The second transfer loop: the auxiliary stack is moved, reversed, onto `B`'s input stack. -/
theorem toIn_iter (y : List Bool) (SA : ∀ k, List (A.Γ k)) (SB : ∀ k, List (B.Γ k))
    (z : List (B.Γ B.k₀)) (v : CSig A B) :
    (flip bind (cmach A B oA iB).step)^[y.length + 1]
        (some ⟨some (Sum.inr (Sum.inr Xfer.toIn)), v,
          cstk A B SA (Function.update SB B.k₀ z) y⟩)
      = some ⟨some (Sum.inr (Sum.inl B.main)), (A.initialState, B.initialState, none),
          cstk A B SA (Function.update SB B.k₀ ((y.map iB.symm).reverse ++ z)) []⟩ := by
  induction y generalizing z v with
  | nil =>
      show (flip bind (cmach A B oA iB).step) _ = _
      show some (TM2.stepAux (cprog A B oA iB (Sum.inr (Sum.inr Xfer.toIn))) v
        (cstk A B SA (Function.update SB B.k₀ z) [])) = _
      have hproj : cstk A B SA (Function.update SB B.k₀ z) ([] : List Bool)
          (Sum.inr (Sum.inr ())) = [] := rfl
      simp only [cprog, TM2.stepAux, hproj, List.head?_nil, List.tail_nil,
        Option.isSome_none, cond_false, List.map_nil, List.reverse_nil, List.nil_append]
      erw [cstk_update_aux]
      rfl
  | cons b t ih =>
      rw [show (b :: t).length + 1 = (t.length + 1) + 1 by simp, Function.iterate_succ_apply]
      have hstep : (flip bind (cmach A B oA iB).step)
            (some ⟨some (Sum.inr (Sum.inr Xfer.toIn)), v,
              cstk A B SA (Function.update SB B.k₀ z) (b :: t)⟩)
          = some ⟨some (Sum.inr (Sum.inr Xfer.toIn)),
              (A.initialState, B.initialState, some b),
              cstk A B SA (Function.update SB B.k₀ (iB.symm b :: z)) t⟩ := by
        show some (TM2.stepAux (cprog A B oA iB (Sum.inr (Sum.inr Xfer.toIn))) v
          (cstk A B SA (Function.update SB B.k₀ z) (b :: t))) = _
        have hproj : cstk A B SA (Function.update SB B.k₀ z) (b :: t)
            (Sum.inr (Sum.inr ())) = b :: t := rfl
        simp only [cprog, TM2.stepAux, hproj, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        erw [cstk_update_aux]
        rw [show cstk A B SA (Function.update SB B.k₀ z) t (Sum.inr (Sum.inl B.k₀))
          = Function.update SB B.k₀ z B.k₀ from rfl, Function.update_self]
        erw [cstk_update_inrl]
        simp only [Function.update_idem]
        rfl
      rw [hstep, ih (iB.symm b :: z) _]
      simp

end CompTM

namespace SizeBd

/-- The maximal number of pushes performed by a single statement. -/
def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

/-- The total number of symbols stored on all stacks. -/
def totalSize {K : Type} [Fintype K] {Γ : K → Type} (S : ∀ k, List (Γ k)) : ℕ :=
  ∑ k : K, (S k).length

variable {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem totalSize_update (S : ∀ k, List (Γ k)) (i : K) (l : List (Γ i)) :
    totalSize (Function.update S i l) + (S i).length = totalSize S + l.length := by
  have h1 : ∀ j, (Function.update S i l j).length
      = Function.update (fun j => (S j).length) i l.length j := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : totalSize (Function.update S i l) = l.length + ∑ j ∈ Finset.univ \ {i}, (S j).length := by
    unfold totalSize
    simp only [h1]
    exact Finset.sum_update_of_mem (Finset.mem_univ i) _ _
  have h3 : (S i).length + ∑ j ∈ Finset.univ.erase i, (S j).length = totalSize S := by
    unfold totalSize
    exact Finset.add_sum_erase Finset.univ (fun j => (S j).length) (Finset.mem_univ i)
  have h4 : Finset.univ \ ({i} : Finset K) = Finset.univ.erase i := by
    ext j; simp [Finset.mem_erase, and_comm]
  rw [h4] at h2
  omega

theorem totalSize_stepAux (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    totalSize (TM2.stepAux q v S).stk ≤ totalSize S + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
      have h := totalSize_update S k (f v :: S k)
      have := ih v (Function.update S k (f v :: S k))
      simp only [TM2.stepAux, pushes, List.length_cons] at *
      omega
  | peek k f q ih => simpa [TM2.stepAux, pushes] using ih _ _
  | pop k f q ih =>
      have h := totalSize_update S k (S k).tail
      have h2 : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
      have := ih (f v (S k).head?) (Function.update S k (S k).tail)
      simp only [TM2.stepAux, pushes] at *
      omega
  | load a q ih => simpa [TM2.stepAux, pushes] using ih _ _
  | branch c q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushes]
      cases hc : c v
      · have := ih₂ v S; simp; omega
      · have := ih₁ v S; simp; omega
  | goto l => simp [TM2.stepAux, pushes, totalSize]
  | halt => simp [TM2.stepAux, pushes, totalSize]


instance instFintypeK (M : FinTM2) : Fintype M.K := M.kFin
instance instFintypeLam (M : FinTM2) : Fintype M.Λ := M.ΛFin

/-- The maximal number of pushes performed by a single step of the machine `M`. -/
def maxPushes (M : FinTM2) : ℕ := Finset.univ.sup fun l : M.Λ => pushes (M.m l)

theorem pushes_le_maxPushes (M : FinTM2) (l : M.Λ) : pushes (M.m l) ≤ maxPushes M :=
  Finset.le_sup (f := fun l : M.Λ => pushes (M.m l)) (Finset.mem_univ l)

theorem totalSize_step {M : FinTM2} {c c' : M.Cfg} (h : M.step c = some c') :
    totalSize c'.stk ≤ totalSize c.stk + maxPushes M := by
  obtain ⟨l, v, S⟩ := c
  match l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hc' : c' = TM2.stepAux (M.m l) v S := by
        have : some c' = some (TM2.stepAux (M.m l) v S) := by
          simpa [FinTM2.step, TM2.step] using h.symm
        exact Option.some_inj.mp this
      subst hc'
      exact le_trans (totalSize_stepAux (M.m l) v S)
        (Nat.add_le_add_left (pushes_le_maxPushes M l) _)

theorem totalSize_iterate {M : FinTM2} (t : ℕ) (c c' : M.Cfg)
    (h : (flip bind M.step)^[t] (some c) = some c') :
    totalSize c'.stk ≤ totalSize c.stk + t * maxPushes M := by
  induction t generalizing c with
  | zero => simp only [Function.iterate_zero, id_eq, Option.some_inj] at h; subst h; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      match hs : M.step c with
      | none =>
          rw [show (flip bind M.step) (some c) = none from hs] at h
          rw [CompTM.iterate_none] at h
          exact absurd h (by simp)
      | some c₁ =>
          rw [show (flip bind M.step) (some c) = some c₁ from hs] at h
          have h1 := ih c₁ h
          have h2 := totalSize_step hs
          have : n * maxPushes M + maxPushes M = (n+1) * maxPushes M := by ring
          omega

/-- The stacks of the initial configuration. -/
theorem initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

/-- The stacks of a halting configuration. -/
theorem haltList_stk (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = Function.update (fun _ => []) M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

theorem totalSize_empty {K : Type} [Fintype K] {Γ : K → Type} :
    totalSize (fun k => ([] : List (Γ k))) = 0 := by simp [totalSize]

theorem totalSize_initList (M : FinTM2) (s : List (M.Γ M.k₀)) :
    totalSize (initList M s).stk = s.length := by
  rw [initList_stk]
  have := totalSize_update (Γ := M.Γ) (fun _ => []) M.k₀ s
  simp only [totalSize_empty, List.length_nil] at this
  omega

theorem totalSize_haltList (M : FinTM2) (s : List (M.Γ M.k₁)) :
    totalSize (haltList M s).stk = s.length := by
  rw [haltList_stk]
  have := totalSize_update (Γ := M.Γ) (fun _ => []) M.k₁ s
  simp only [totalSize_empty, List.length_nil] at this
  omega


/-- Evaluation of a polynomial with natural-number coefficients is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

end SizeBd

namespace CompTM

open SizeBd

variable {A B : FinTM2} (oA : A.Γ A.k₁ ≃ Bool) (iB : B.Γ B.k₀ ≃ Bool)

theorem cstk_empty : cstk A B (fun _ => []) (fun _ => []) [] = fun _ => [] := by
  funext k
  match k with
  | .inl a => rfl
  | .inr (.inl b) => rfl
  | .inr (.inr u) => rfl

/-- The initial configuration of the composed machine is the initial configuration of `A`,
transported to the composed machine. -/
theorem initList_comp (u : List (A.Γ A.k₀)) :
    initList (cmach A B oA iB) u
      = cfgA A B (initList A u) B.initialState none (fun _ => []) [] := by
  have hstk : (initList (cmach A B oA iB) u).stk
      = (cfgA A B (initList A u) B.initialState none (fun _ => []) []).stk := by
    show (initList (cmach A B oA iB) u).stk = cstk A B (initList A u).stk (fun _ => []) []
    rw [initList_stk, initList_stk]
    rw [show (fun _ => []) = cstk A B (fun _ => []) (fun _ => []) ([] : List Bool) from
      (cstk_empty (A := A) (B := B)).symm]
    exact cstk_update_inl _ _ _ _ _
  exact congrArg (fun S => (⟨_, _, S⟩ : TM2.Cfg (CGam A B) (CLbl A B) (CSig A B))) hstk

/-- A halting configuration of the composed machine is a halting configuration of `B`,
transported to the composed machine. -/
theorem haltList_comp (w : List (B.Γ B.k₁)) :
    haltList (cmach A B oA iB) w
      = cfgB A B (haltList B w) A.initialState none (fun _ => []) [] := by
  have hstk : (haltList (cmach A B oA iB) w).stk
      = (cfgB A B (haltList B w) A.initialState none (fun _ => []) []).stk := by
    show (haltList (cmach A B oA iB) w).stk = cstk A B (fun _ => []) (haltList B w).stk []
    rw [haltList_stk, haltList_stk]
    rw [show (fun _ => []) = cstk A B (fun _ => []) (fun _ => []) ([] : List Bool) from
      (cstk_empty (A := A) (B := B)).symm]
    exact cstk_update_inrl _ _ _ _ _
  exact congrArg (fun S => (⟨_, _, S⟩ : TM2.Cfg (CGam A B) (CLbl A B) (CSig A B))) hstk


/-- The composed machine, run on an input `u` for `A`, halts with `B`'s output `w'`, in
`sA + sB + 2 * (|w| + 1)` steps, where `w` is `A`'s output. -/
theorem comp_run (u : List (A.Γ A.k₀)) (w : List (A.Γ A.k₁)) (w' : List (B.Γ B.k₁))
    (sA sB : ℕ)
    (hA : (flip bind (TM2.step A.m))^[sA] (some (initList A u)) = some (haltList A w))
    (hB : (flip bind (TM2.step B.m))^[sB]
        (some (initList B (List.map iB.symm (List.map oA w)))) = some (haltList B w')) :
    (flip bind (cmach A B oA iB).step)^[sB + ((w.length + 1) + ((w.length + 1) + sA))]
        (some (initList (cmach A B oA iB) u))
      = some (haltList (cmach A B oA iB) w') := by
  have split : ∀ (m n : ℕ) (x : Option (TM2.Cfg (CGam A B) (CLbl A B) (CSig A B))),
      (flip bind (cmach A B oA iB).step)^[m + n] x
        = (flip bind (cmach A B oA iB).step)^[m] ((flip bind (cmach A B oA iB).step)^[n] x) :=
    fun m n x => Function.iterate_add_apply _ m n x
  have hupdA : Function.update (fun k => ([] : List (A.Γ k))) A.k₁ [] = fun k => [] :=
    Function.update_eq_self _ _
  have hupdB : Function.update (fun k => ([] : List (B.Γ k))) B.k₀ [] = fun k => [] :=
    Function.update_eq_self _ _
  -- the configuration reached once `A` has halted
  have e0 : (flip bind (cmach A B oA iB).step)^[sA] (some (initList (cmach A B oA iB) u))
      = some (⟨some (Sum.inr (Sum.inr Xfer.toAux)), (A.initialState, B.initialState, none),
          cstk A B (Function.update (fun k => []) A.k₁ w) (fun k => []) []⟩ :
          TM2.Cfg (CGam A B) (CLbl A B) (CSig A B)) := by
    rw [initList_comp,
      iter_liftA oA iB sA (initList A u) (haltList A w) B.initialState none (fun k => []) [] hA]
    unfold cfgA
    rw [haltList_stk]
    rfl
  -- the first transfer loop
  have e1 : (flip bind (cmach A B oA iB).step)^[w.length + 1]
        (some (⟨some (Sum.inr (Sum.inr Xfer.toAux)), (A.initialState, B.initialState, none),
          cstk A B (Function.update (fun k => []) A.k₁ w) (fun k => []) []⟩ :
          TM2.Cfg (CGam A B) (CLbl A B) (CSig A B)))
      = some (⟨some (Sum.inr (Sum.inr Xfer.toIn)), (A.initialState, B.initialState, none),
          cstk A B (fun k => []) (Function.update (fun k => []) B.k₀ [])
            (List.map oA w).reverse⟩ : TM2.Cfg (CGam A B) (CLbl A B) (CSig A B)) := by
    rw [toAux_iter oA iB w (fun k => []) (fun k => []) [] _, hupdA, hupdB, List.append_nil]
    rfl
  -- the second transfer loop
  have e2 : (flip bind (cmach A B oA iB).step)^[w.length + 1]
        (some (⟨some (Sum.inr (Sum.inr Xfer.toIn)), (A.initialState, B.initialState, none),
          cstk A B (fun k => []) (Function.update (fun k => []) B.k₀ [])
            (List.map oA w).reverse⟩ : TM2.Cfg (CGam A B) (CLbl A B) (CSig A B)))
      = some (cfgB A B (initList B (List.map iB.symm (List.map oA w))) A.initialState none
          (fun k => []) []) := by
    rw [show w.length + 1 = ((List.map oA w).reverse).length + 1 by simp,
      toIn_iter oA iB (List.map oA w).reverse (fun k => []) (fun k => []) [] _]
    unfold cfgB
    rw [initList_stk, List.append_nil, ← List.map_reverse, List.reverse_reverse]
    rfl
  -- `B` runs to completion
  have e3 : (flip bind (cmach A B oA iB).step)^[sB]
        (some (cfgB A B (initList B (List.map iB.symm (List.map oA w))) A.initialState none
          (fun k => []) []))
      = some (haltList (cmach A B oA iB) w') := by
    rw [iter_liftB oA iB sB (initList B (List.map iB.symm (List.map oA w))) (haltList B w')
      A.initialState none (fun k => []) [] hB, haltList_comp]
    rfl
  have s1 := split sB ((w.length + 1) + ((w.length + 1) + sA))
    (some (initList (cmach A B oA iB) u))
  have s2 := split (w.length + 1) ((w.length + 1) + sA) (some (initList (cmach A B oA iB) u))
  have s3 := split (w.length + 1) sA (some (initList (cmach A B oA iB) u))
  refine s1.trans ?_
  refine (congrArg (fun y => (flip bind (cmach A B oA iB).step)^[sB] y) ?_).trans e3
  refine s2.trans ?_
  refine (congrArg (fun y => (flip bind (cmach A B oA iB).step)^[w.length + 1] y) ?_).trans e2
  refine s3.trans ?_
  exact (congrArg (fun y => (flip bind (cmach A B oA iB).step)^[w.length + 1] y) e0).trans e1

end CompTM

open PvsNP BitstringEncoding in
/-- **Composition of polynomial-time functions.**  If `f : α → β` and `g : β → γ` are both
computable in polynomial time (with respect to the canonical bitstring encodings), then so is
`g ∘ f`.

The machine for `g ∘ f` runs the machine `A` for `f`, then moves `A`'s output stack, one symbol
at a time, onto an auxiliary stack and from there onto the input stack of the machine `B` for
`g` (the two reversals cancel), and finally runs `B`.  The number of steps of the transfer is
`2 * (|f a| + 1)`, and since a single step of `A` pushes at most `maxPushes A` symbols, the
length of `A`'s output is at most `|a| + maxPushes A * time_A(|a|)`, which is polynomial in
`|a|`; substituting this bound into the time polynomial of `B` gives a polynomial time bound
for the composed machine. -/
theorem solution {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : β → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by
  obtain ⟨MA⟩ := hf
  obtain ⟨MB⟩ := hg
  set cA := SizeBd.maxPushes MA.tm with hcA
  set Q : Polynomial ℕ := Polynomial.X + Polynomial.C cA * MA.time with hQ
  have hQeval : ∀ n : ℕ, Q.eval n = n + cA * MA.time.eval n := by
    intro n; simp [hQ]
  refine ⟨{ tm := CompTM.cmach MA.tm MB.tm MA.outputAlphabet MB.inputAlphabet
            inputAlphabet := MA.inputAlphabet
            outputAlphabet := MB.outputAlphabet
            time := MA.time + 2 * Q + Polynomial.C 2 + MB.time.comp Q
            outputsFun := fun a => ?_ }⟩
  have hA := MA.outputsFun a
  have hB := MB.outputsFun (f a)
  set u := List.map MA.inputAlphabet.invFun ((BitstringEncoding.toEncoding (α := α)).encode a) with hu
  set wA := List.map MA.outputAlphabet.invFun ((BitstringEncoding.toEncoding (α := β)).encode (f a)) with hwA
  set wB := List.map MB.outputAlphabet.invFun ((BitstringEncoding.toEncoding (α := γ)).encode (g (f a))) with hwB
  set n := ((BitstringEncoding.toEncoding (α := α)).encode a).length with hn
  -- the run of `A`
  have hA' : (flip bind (TM2.step MA.tm.m))^[hA.steps] (some (initList MA.tm u))
      = some (haltList MA.tm wA) := hA.evals_in_steps
  -- the run of `B`
  have hmap : List.map MB.inputAlphabet.symm (List.map MA.outputAlphabet wA)
      = List.map MB.inputAlphabet.invFun ((BitstringEncoding.toEncoding (α := β)).encode (f a)) := by
    simp [hwA, List.map_map]
  have hB' : (flip bind (TM2.step MB.tm.m))^[hB.steps]
      (some (initList MB.tm (List.map MB.inputAlphabet.symm
        (List.map MA.outputAlphabet wA)))) = some (haltList MB.tm wB) := by
    rw [hmap]; exact hB.evals_in_steps
  -- the length of `A`'s output is polynomially bounded
  have hlen : wA.length ≤ Q.eval n := by
    have h1 := SizeBd.totalSize_iterate hA.steps (initList MA.tm u) (haltList MA.tm wA) hA'
    rw [SizeBd.totalSize_initList, SizeBd.totalSize_haltList] at h1
    have h2 : u.length = n := by simp [hu, hn]
    have h3 : hA.steps ≤ MA.time.eval n := hA.steps_le_m
    have h4 : hA.steps * cA ≤ MA.time.eval n * cA := Nat.mul_le_mul_right _ h3
    rw [hQeval]
    calc wA.length ≤ u.length + hA.steps * cA := h1
      _ ≤ n + MA.time.eval n * cA := by omega
      _ = n + cA * MA.time.eval n := by ring
  -- the time bound
  have hsB : hB.steps ≤ MB.time.eval (Q.eval n) := by
    refine le_trans hB.steps_le_m ?_
    refine SizeBd.eval_mono _ ?_
    have : ((BitstringEncoding.toEncoding (α := β)).encode (f a)).length = wA.length := by simp [hwA]
    omega
  refine ⟨⟨hB.steps + ((wA.length + 1) + ((wA.length + 1) + hA.steps)), ?_⟩, ?_⟩
  · exact CompTM.comp_run MA.outputAlphabet MB.inputAlphabet u wA wB hA.steps hB.steps hA' hB'
  · have hT : (MA.time + 2 * Q + Polynomial.C 2 + MB.time.comp Q).eval n
        = MA.time.eval n + 2 * Q.eval n + 2 + MB.time.eval (Q.eval n) := by
      simp [Polynomial.eval_comp]
    have h3 : hA.steps ≤ MA.time.eval n := hA.steps_le_m
    show hB.steps + ((wA.length + 1) + ((wA.length + 1) + hA.steps))
      ≤ (MA.time + 2 * Q + Polynomial.C 2 + MB.time.comp Q).eval n
    rw [hT]
    omega
