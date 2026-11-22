-- Prove2me | solution 1 for ShiShallow.exists_fanout_embedded_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T19:52:48.242299+00:00
-- url     : https://prove2.me/submissions/c5bb12c8-da0d-417e-80ca-6085e88825e1

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

EMBEDDED FAN-OUT as an explicit pullback on the big register.

`g : Fin (n + n) -> Fin N` is an arbitrary INJECTIVE wire map into a register of any size.
The circuit built here is ONE layer of `n` CNOTs, the `j`-th with control `g (castAdd n j)`
and target `g (natAdd n j)`; it XORs each first-half wire into the matching second-half wire
and touches no other wire of `Fin N`.

Two things are deliberately avoided.  (1) We do NOT go through the square fan-out on
`Fin (n + n)` plus a circuit embedding: the map straddles two tensor blocks, so no transport
lemma applies.  (2) Consequently the update map `u` is defined by RECURSION ON THE GATE LIST,
not by `Fin.addCases` -- there is no `addCases` in this file at all, so the
`Fin.natAdd_eq_addNat` simp trap (core `Init/Data/Fin/Lemmas.lean:738`, `@[simp]`, fires
exactly in the square case `Fin n -> Fin (n + n)` that `g`'s domain lives in) can only bite
inside the two `simp only` sets that mention `Fin.natAdd`, and both erase it explicitly.

GATE ORIENTATION, verified against the semantic clause: `Def_ShiShallow_Core.lean:33-34`
defines `cnotState i j _ psi = fun x => psi (Function.update x j (xor (x j) (x i)))`
(docstring: "CNOT with control `i`, target `j`"), and `Instr.apply` (`:48`) sends
`.cnot i j hij` to `cnotState i j hij`.  So the FIRST argument of `Instr.cnot` is the CONTROL
and the SECOND is the TARGET.  The fan-out must overwrite the second half, hence
control `g (castAdd n j)`, target `g (natAdd n j)`.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

/-! ## Wire facts

`(Fin.castAdd n j).val` is `j.val` and `(Fin.natAdd n j).val` is `n + j.val`, both by `rfl`
(`Fin.val_castAdd`, core `Init/Data/Fin/Lemmas.lean:525`; `Fin.val_natAdd`, `:684`). -/

private theorem shiFE_cast_ne_nat {n : ℕ} (j k : Fin n) :
    (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n k := by
  intro h
  have h2 : (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  have hj := j.isLt
  omega

-- The `congrArg` below must be given the FULLY ASCRIBED equation: with expected type
-- `(j : ℕ) = (k : ℕ)` Lean unifies `?f ?a = ?f ?b` as `f := Fin.val, a := j, b := k` and then
-- demands `h : j = k`.  Ascribing both sides as `.val` of the `castAdd`s pins the right
-- `a`/`b`; `Fin.ext` then accepts it because `Fin.val_castAdd` is `rfl`.
private theorem shiFE_cast_inj {n : ℕ} {j k : Fin n}
    (h : (Fin.castAdd n j : Fin (n + n)) = Fin.castAdd n k) : j = k := by
  have h2 : ((Fin.castAdd n j : Fin (n + n)) : ℕ) = ((Fin.castAdd n k : Fin (n + n)) : ℕ) :=
    congrArg Fin.val h
  exact Fin.ext h2

private theorem shiFE_nat_inj {n : ℕ} {j k : Fin n}
    (h : (Fin.natAdd n j : Fin (n + n)) = Fin.natAdd n k) : j = k := by
  have h2 : n + (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

/-! The same three facts pushed forward along the injection `g`. -/

private theorem shiFE_g_cast_ne_nat {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) (j k : Fin n) :
    g (Fin.castAdd n j) ≠ g (Fin.natAdd n k) :=
  fun h => shiFE_cast_ne_nat j k (hg h)

private theorem shiFE_g_cast_inj {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) {j k : Fin n}
    (h : g (Fin.castAdd n j) = g (Fin.castAdd n k)) : j = k :=
  shiFE_cast_inj (hg h)

private theorem shiFE_g_nat_inj {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) {j k : Fin n}
    (h : g (Fin.natAdd n j) = g (Fin.natAdd n k)) : j = k :=
  shiFE_nat_inj (hg h)

/-! ## The layer -/

private def shiFE_gate {n N : ℕ} (g : Fin (n + n) → Fin N) (hg : Function.Injective g)
    (j : Fin n) : Instr N :=
  Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j)) (shiFE_g_cast_ne_nat hg j j)

private theorem shiFE_disj {n N : ℕ} (g : Fin (n + n) → Fin N) (hg : Function.Injective g)
    {j k : Fin n} (hjk : j ≠ k) :
    Disjoint (shiFE_gate g hg j).support (shiFE_gate g hg k).support := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [shiFE_gate, Instr.support, Finset.mem_insert, Finset.mem_singleton,
    -Fin.natAdd_eq_addNat] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with h | h
    · exact hjk (shiFE_g_cast_inj hg h)
    · exact shiFE_g_cast_ne_nat hg j k h
  · rcases hb with h | h
    · exact shiFE_g_cast_ne_nat hg k j h.symm
    · exact hjk (shiFE_g_nat_inj hg h)

private theorem shiFE_layerOk {n N : ℕ} (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) :
    LayerOk ((List.finRange n).map (shiFE_gate g hg)) := by
  rw [LayerOk, List.pairwise_map]
  exact (List.nodup_finRange n).imp (fun h => shiFE_disj g hg h)

/-! ## The update map

Defined by recursion on the list of CNOTs already folded in.  The XORed-in value always reads
the ORIGINAL `Y`, never the partially updated state, so the map is the SIMULTANEOUS update and
no `Nodup` hypothesis is needed to state it. -/

private def shiFE_upd {n N : ℕ} (g : Fin (n + n) → Fin N) :
    List (Fin n) → Bits N → Bits N
  | [], Y => Y
  | j :: rest, Y =>
      Function.update (shiFE_upd g rest Y) (g (Fin.natAdd n j))
        (xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))

private theorem shiFE_upd_nil {n N : ℕ} (g : Fin (n + n) → Fin N) (Y : Bits N) :
    shiFE_upd g ([] : List (Fin n)) Y = Y := by
  simp only [shiFE_upd]

private theorem shiFE_upd_cons {n N : ℕ} (g : Fin (n + n) → Fin N) (j : Fin n)
    (rest : List (Fin n)) (Y : Bits N) :
    shiFE_upd g (j :: rest) Y
      = Function.update (shiFE_upd g rest Y) (g (Fin.natAdd n j))
          (xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j)))) := by
  simp only [shiFE_upd, -Fin.natAdd_eq_addNat]

/-- Off the image of the second half, the update does nothing. -/
private theorem shiFE_upd_other {n N : ℕ} (g : Fin (n + n) → Fin N) :
    ∀ (js : List (Fin n)) (Y : Bits N) (k : Fin N),
      (∀ j ∈ js, g (Fin.natAdd n j) ≠ k) → shiFE_upd g js Y k = Y k := by
  intro js
  induction js with
  | nil =>
      intro Y k _
      rw [shiFE_upd_nil]
  | cons j rest ih =>
      intro Y k hk
      rw [shiFE_upd_cons,
        Function.update_of_ne (Ne.symm (hk j (List.mem_cons.2 (Or.inl rfl)))),
        ih Y k (fun a ha => hk a (List.mem_cons.2 (Or.inr ha)))]

/-- On the image of the second half, the update XORs the matching first-half wire in. -/
private theorem shiFE_upd_nat {n N : ℕ} (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) :
    ∀ (js : List (Fin n)) (Y : Bits N) (j : Fin n), j ∈ js →
      shiFE_upd g js Y (g (Fin.natAdd n j))
        = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))) := by
  intro js
  induction js with
  | nil =>
      intro Y j hj
      simp at hj
  | cons k rest ih =>
      intro Y j hj
      by_cases hkj : k = j
      · subst hkj
        rw [shiFE_upd_cons, Function.update_self]
      · have hjr : j ∈ rest := by
          rcases List.mem_cons.1 hj with h1 | h1
          · exact absurd h1.symm hkj
          · exact h1
        rw [shiFE_upd_cons,
          Function.update_of_ne (fun h => hkj (shiFE_g_nat_inj hg h).symm),
          ih Y j hjr]

/-! ## Folding the layer -/

private theorem shiFE_runLayer_nil {N : ℕ} (ψ : QState N) : runLayer [] ψ = ψ := by
  simp only [runLayer, List.foldl_nil]

private theorem shiFE_runLayer_cons {N : ℕ} (a : Instr N) (as : List (Instr N))
    (ψ : QState N) : runLayer (a :: as) ψ = runLayer as (a.apply ψ) := by
  simp only [runLayer, List.foldl_cons]

private theorem shiFE_runLayered_single {N : ℕ} (l : List (Instr N)) (φ : QState N) :
    runLayered [l] φ = runLayer l φ := by
  simp only [runLayered, List.foldl_cons, List.foldl_nil]

/-- One gate of the layer, evaluated at a point.  Definitional: `shiFE_gate` delta-reduces,
`Instr.apply` iota-reduces on the `.cnot` constructor, `cnotState` delta/beta-reduces. -/
private theorem shiFE_gate_apply {n N : ℕ} (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) (j : Fin n) (φ : QState N) (w : Bits N) :
    (shiFE_gate g hg j).apply φ w
      = φ (Function.update w (g (Fin.natAdd n j))
            (xor (w (g (Fin.natAdd n j))) (w (g (Fin.castAdd n j))))) :=
  rfl

private theorem shiFE_fold {n N : ℕ} (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) :
    ∀ js : List (Fin n), js.Nodup → ∀ (φ : QState N) (x : Bits N),
      runLayer (js.map (shiFE_gate g hg)) φ x = φ (shiFE_upd g js x) := by
  intro js
  induction js with
  | nil =>
      intro _ φ x
      rw [List.map_nil, shiFE_runLayer_nil, shiFE_upd_nil]
      all_goals rfl
  | cons j rest ih =>
      intro hjs φ x
      have hj : j ∉ rest := (List.nodup_cons.1 hjs).1
      have hrest : rest.Nodup := (List.nodup_cons.1 hjs).2
      -- the partially updated state already agrees with `x` on both wires this gate reads
      have h1 : shiFE_upd g rest x (g (Fin.natAdd n j)) = x (g (Fin.natAdd n j)) := by
        refine shiFE_upd_other g rest x _ ?_
        intro a ha h
        have hae : a = j := shiFE_g_nat_inj hg h
        subst hae
        exact hj ha
      have h2 : shiFE_upd g rest x (g (Fin.castAdd n j)) = x (g (Fin.castAdd n j)) := by
        refine shiFE_upd_other g rest x _ ?_
        intro a _ h
        exact shiFE_g_cast_ne_nat hg j a h.symm
      -- `ih`'s STATE argument is `x`; `shiFE_upd g rest x` appears on the RIGHT of its
      -- equation, not as an argument.
      rw [List.map_cons, shiFE_runLayer_cons, ih hrest ((shiFE_gate g hg j).apply φ) x,
        shiFE_gate_apply g hg j φ (shiFE_upd g rest x), h1, h2, shiFE_upd_cons]
      all_goals rfl

/-- **The embedded fan-out, as an explicit pullback on the big register.**  For any injective
wire map `g : Fin (n + n) → Fin N` there is a single well-formed layer on `Fin N` whose
`runLayered` is pullback along an explicit bit-string update `u`; `u` XORs each first-half
wire `g (castAdd n j)` into the matching second-half wire `g (natAdd n j)` and fixes every
wire outside the image of the second half. -/
theorem solution (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g) :
    ∃ (c : Layered N) (u : Bits N → Bits N),
      (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
      ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
            = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
      ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 1 := by
  refine ⟨[(List.finRange n).map (shiFE_gate g hg)], shiFE_upd g (List.finRange n),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro Φ
    funext Y
    rw [shiFE_runLayered_single,
      shiFE_fold g hg (List.finRange n) (List.nodup_finRange n) Φ Y]
    all_goals rfl
  · intro Y j
    exact shiFE_upd_nat g hg (List.finRange n) Y j (List.mem_finRange j)
  · intro Y k hk
    exact shiFE_upd_other g (List.finRange n) Y k (fun a _ => hk a)
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact shiFE_layerOk g hg
  · simp [depth]
