-- Prove2me | solution 1 for ShiShallow.explicit_embedded_fanout_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-18T11:27:10.441826+00:00
-- url     : https://prove2.me/submissions/979989c2-6a40-4591-bb88-cb0890b6544b

/-
EXPLICIT-2b.  The EMBEDDED fan-out's circuit as a LITERAL TERM.

`ShiShallow.exists_fanout_embedded_pullback` fixes its circuit only up to ACTION, so the
gate list is undetermined and nothing built from it has a determined `ShiBQP.encCirc`
image.  This file carries the same five conjuncts with the circuit PINNED:

  c = [(List.finRange n).map (fun j => Instr.cnot (g (castAdd n j)) (g (natAdd n j)) _)]

one layer, one CNOT per `j`, low-half image controlling high-half image, the distinctness
side condition supplied as an INLINE proof term so that no private name enters the
statement.  The pullback `u` is pinned too: on a wire that is `g (natAdd n j)` for some
`j` it XORs with the partner `g (castAdd n j)`, and elsewhere it is the identity; `g`
injective makes that `j` unique, so the classical choice is determinate.

FINDING on the layer's disjointness obligation.  `LayerOk` asks for pairwise disjoint
supports: gate `j` touches `{g (castAdd n j), g (natAdd n j)}`, so for `j != k` all FOUR
wires must be distinct.  Injectivity of `g` alone DOES suffice, and no extra hypothesis is
needed: in `Fin (n + n)` the four preimages `castAdd n j, natAdd n j, castAdd n k,
natAdd n k` are pairwise distinct (the two `castAdd`s differ because `j != k`, the two
`natAdd`s likewise, and a `castAdd` never meets a `natAdd` since its value is `< n` while
the other's is `n + _`), and `g` transports that distinctness forward.  The existence
theorem is therefore NOT refutable here.

The final conjunct is an UNCONDITIONAL check at a NON-IDENTITY embedding: `n = 2`,
`N = 6`, `g v = v + 1`.  The template then instantiates to the two literal gates
`cnot 1 3` and `cnot 2 4`, and the pullback sends the input with wires `{1, 5}` set to
the string with wires `{1, 3, 5}` set: the XOR fires on the high-half image `3`
(partner `1` is set), does not fire on `4` (partner `2` is clear), and the wires `0` and
`5` outside the range of `g` on the high half are left exactly alone.  An identity
embedding would not have tested the composition with `g` at all.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false


open ShiShallow

/-! ## Index arithmetic in `Fin (n + n)`

`(Fin.castAdd n j).val` is `j.val` and `(Fin.natAdd n j).val` is `n + j.val`, both by
`rfl`, which is why the inline distinctness proof term in the statement typechecks. -/

private theorem castNeNat {n : ℕ} (j k : Fin n) :
    (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n k := by
  intro h
  have h2 : (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  have hj := j.isLt
  omega

private theorem castInj {n : ℕ} {j k : Fin n}
    (h : (Fin.castAdd n j : Fin (n + n)) = Fin.castAdd n k) : j = k := by
  have h2 : ((Fin.castAdd n j : Fin (n + n)) : ℕ) = ((Fin.castAdd n k : Fin (n + n)) : ℕ) :=
    congrArg Fin.val h
  exact Fin.ext h2

private theorem natInj {n : ℕ} {j k : Fin n}
    (h : (Fin.natAdd n j : Fin (n + n)) = Fin.natAdd n k) : j = k := by
  have h2 : n + (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

private theorem gCastNeGNat {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) (j k : Fin n) :
    g (Fin.castAdd n j) ≠ g (Fin.natAdd n k) :=
  fun h => castNeNat j k (hg h)

private theorem gNatInj {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) {j k : Fin n}
    (h : g (Fin.natAdd n j) = g (Fin.natAdd n k)) : j = k :=
  natInj (hg h)

/-! ## The gates and the layer -/

/-- Control `g (castAdd n j)` (low-half image), target `g (natAdd n j)` (high-half image). -/
private def embGate {n N : ℕ} (g : Fin (n + n) → Fin N) (hg : Function.Injective g)
    (j : Fin n) : Instr N :=
  Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j)) (gCastNeGNat hg j j)

private theorem embDisj {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g)
    {j k : Fin n} (hjk : j ≠ k) :
    Disjoint (embGate g hg j).support (embGate g hg k).support := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [embGate, Instr.support, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with h | h
    · exact hjk (castInj (hg h))
    · exact gCastNeGNat hg j k h
  · rcases hb with h | h
    · exact gCastNeGNat hg k j h.symm
    · exact hjk (gNatInj hg h)

private theorem embLayerOk {n N : ℕ} (g : Fin (n + n) → Fin N) (hg : Function.Injective g) :
    LayerOk ((List.finRange n).map (embGate g hg)) := by
  rw [LayerOk, List.pairwise_map]
  exact (List.nodup_finRange n).imp (fun h => embDisj hg h)

/-! ## The pullback map -/

/-- The pullback after the gates for `js` have fired. -/
private noncomputable def embV {n N : ℕ} (g : Fin (n + n) → Fin N) (js : List (Fin n))
    (x : Bits N) : Bits N :=
  fun k => if h : ∃ j : Fin n, j ∈ js ∧ g (Fin.natAdd n j) = k
           then xor (x k) (x (g (Fin.castAdd n h.choose))) else x k

/-- The pinned pullback of the whole layer. -/
private noncomputable def embU {n N : ℕ} (g : Fin (n + n) → Fin N) (x : Bits N) : Bits N :=
  fun k => if h : ∃ j : Fin n, g (Fin.natAdd n j) = k
           then xor (x k) (x (g (Fin.castAdd n h.choose))) else x k

private theorem embV_mem {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g)
    {js : List (Fin n)} {j : Fin n} (hj : j ∈ js) (x : Bits N) :
    embV g js x (g (Fin.natAdd n j))
      = xor (x (g (Fin.natAdd n j))) (x (g (Fin.castAdd n j))) := by
  have hex : ∃ i : Fin n, i ∈ js ∧ g (Fin.natAdd n i) = g (Fin.natAdd n j) := ⟨j, hj, rfl⟩
  simp only [embV]
  rw [dif_pos hex, gNatInj hg hex.choose_spec.2]

private theorem embV_not {n N : ℕ} {g : Fin (n + n) → Fin N}
    {js : List (Fin n)} {k : Fin N} (hk : ∀ j ∈ js, g (Fin.natAdd n j) ≠ k) (x : Bits N) :
    embV g js x k = x k := by
  have hex : ¬ ∃ j : Fin n, j ∈ js ∧ g (Fin.natAdd n j) = k := by
    intro h
    obtain ⟨j, hj, hjk⟩ := h
    exact hk j hj hjk
  simp only [embV]
  rw [dif_neg hex]

private theorem embU_mem {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g)
    (j : Fin n) (x : Bits N) :
    embU g x (g (Fin.natAdd n j))
      = xor (x (g (Fin.natAdd n j))) (x (g (Fin.castAdd n j))) := by
  have hex : ∃ i : Fin n, g (Fin.natAdd n i) = g (Fin.natAdd n j) := ⟨j, rfl⟩
  simp only [embU]
  rw [dif_pos hex, gNatInj hg hex.choose_spec]

private theorem embU_not {n N : ℕ} {g : Fin (n + n) → Fin N} {k : Fin N}
    (hk : ∀ j : Fin n, g (Fin.natAdd n j) ≠ k) (x : Bits N) : embU g x k = x k := by
  have hex : ¬ ∃ j : Fin n, g (Fin.natAdd n j) = k := by
    intro h
    obtain ⟨j, hjk⟩ := h
    exact hk j hjk
  simp only [embU]
  rw [dif_neg hex]

private theorem embV_nil {n N : ℕ} (g : Fin (n + n) → Fin N) (x : Bits N) :
    embV g [] x = x := by
  funext k
  refine embV_not ?_ x
  intro j hj
  simp at hj

private theorem embV_cons {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g)
    (j : Fin n) (rest : List (Fin n)) (x : Bits N) :
    Function.update (embV g rest x) (g (Fin.natAdd n j))
        (xor (x (g (Fin.natAdd n j))) (x (g (Fin.castAdd n j))))
      = embV g (j :: rest) x := by
  funext k
  by_cases hkj : g (Fin.natAdd n j) = k
  · subst hkj
    rw [Function.update_self, embV_mem hg (List.mem_cons.2 (Or.inl rfl)) x]
  · rw [Function.update_of_ne (fun h => hkj h.symm)]
    by_cases hr : ∃ i : Fin n, i ∈ rest ∧ g (Fin.natAdd n i) = k
    · obtain ⟨i, hi, hik⟩ := hr
      subst hik
      rw [embV_mem hg hi x, embV_mem hg (List.mem_cons_of_mem j hi) x]
    · have hrest : ∀ i ∈ rest, g (Fin.natAdd n i) ≠ k := by
        intro i hi hik
        exact hr ⟨i, hi, hik⟩
      have hcons : ∀ i ∈ j :: rest, g (Fin.natAdd n i) ≠ k := by
        intro i hi hik
        rcases List.mem_cons.1 hi with h1 | h1
        · subst h1
          exact hkj hik
        · exact hrest i h1 hik
      rw [embV_not hrest x, embV_not hcons x]

private theorem embV_full {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g)
    (x : Bits N) : embV g (List.finRange n) x = embU g x := by
  funext k
  by_cases h : ∃ j : Fin n, g (Fin.natAdd n j) = k
  · obtain ⟨j, hj⟩ := h
    subst hj
    rw [embV_mem hg (List.mem_finRange j) x, embU_mem hg j x]
  · have hno : ∀ j : Fin n, g (Fin.natAdd n j) ≠ k := by
      intro j hjk
      exact h ⟨j, hjk⟩
    rw [embV_not (fun i _ => hno i) x, embU_not hno x]

/-! ## Running the layer -/

private theorem runLayer_nil' {N : ℕ} (ψ : QState N) : runLayer [] ψ = ψ := by
  simp only [runLayer, List.foldl_nil]

private theorem runLayer_cons' {N : ℕ} (a : Instr N) (gs : List (Instr N)) (ψ : QState N) :
    runLayer (a :: gs) ψ = runLayer gs (a.apply ψ) := by
  simp only [runLayer, List.foldl_cons]

private theorem runLayered_single' {N : ℕ} (l : List (Instr N)) (φ : QState N) :
    runLayered [l] φ = runLayer l φ := by
  simp only [runLayered, List.foldl_cons, List.foldl_nil]

private theorem embGate_apply {n N : ℕ} {g : Fin (n + n) → Fin N}
    (hg : Function.Injective g) (j : Fin n) (φ : QState N) (w : Bits N) :
    (embGate g hg j).apply φ w
      = φ (Function.update w (g (Fin.natAdd n j))
            (xor (w (g (Fin.natAdd n j))) (w (g (Fin.castAdd n j))))) :=
  rfl

private theorem embFold {n N : ℕ} {g : Fin (n + n) → Fin N} (hg : Function.Injective g) :
    ∀ js : List (Fin n), js.Nodup → ∀ (φ : QState N) (x : Bits N),
      runLayer (js.map (embGate g hg)) φ x = φ (embV g js x) := by
  intro js
  induction js with
  | nil =>
      intro _ φ x
      simp only [List.map_nil, runLayer_nil', embV_nil]
  | cons j rest ih =>
      intro hjs φ x
      have hj : j ∉ rest := (List.nodup_cons.1 hjs).1
      have hrest : rest.Nodup := (List.nodup_cons.1 hjs).2
      have ht : embV g rest x (g (Fin.natAdd n j)) = x (g (Fin.natAdd n j)) := by
        refine embV_not ?_ x
        intro i hi hik
        have hij : i = j := gNatInj hg hik
        subst hij
        exact hj hi
      have hc : embV g rest x (g (Fin.castAdd n j)) = x (g (Fin.castAdd n j)) := by
        refine embV_not ?_ x
        intro i _ hik
        exact gCastNeGNat hg j i hik.symm
      rw [List.map_cons, runLayer_cons', ih hrest ((embGate g hg j).apply φ) x,
        embGate_apply hg j φ (embV g rest x), ht, hc, embV_cons hg j rest x]

/-! ## The embedded fan-out, circuit pinned -/

private theorem embSpec {n N : ℕ} (g : Fin (n + n) → Fin N) (hg : Function.Injective g) :
    (∀ Φ : QState N, runLayered [(List.finRange n).map (embGate g hg)] Φ
        = fun Y => Φ (embU g Y))
      ∧ (∀ (Y : Bits N) (j : Fin n), embU g Y (g (Fin.natAdd n j))
            = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
      ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) →
            embU g Y k = Y k)
      ∧ (∀ l ∈ [(List.finRange n).map (embGate g hg)], LayerOk l)
      ∧ depth [(List.finRange n).map (embGate g hg)] = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Φ
    funext Y
    rw [runLayered_single', embFold hg (List.finRange n) (List.nodup_finRange n) Φ Y]
    exact congrArg Φ (embV_full hg Y)
  · intro Y j
    exact embU_mem hg j Y
  · intro Y k hk
    exact embU_not hk Y
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact embLayerOk g hg
  · simp [depth]

/-! ## The public theorem -/

theorem solution :
    (∀ (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g),
      ∃ (c : Layered N) (u : Bits N → Bits N),
        c = [(List.finRange n).map (fun j : Fin n =>
              Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j))
                (fun h => by
                  have hj : (j : ℕ) < n := j.isLt
                  have hv : (j : ℕ) = n + (j : ℕ) := congrArg Fin.val (hg h)
                  omega))]
        ∧ u = (fun (x : Bits N) (k : Fin N) =>
              if h : ∃ j : Fin n, g (Fin.natAdd n j) = k
                then xor (x k) (x (g (Fin.castAdd n h.choose))) else x k)
        ∧ (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
              = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
        ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1)
    ∧ (∃ (c : Layered 6) (u : Bits 6 → Bits 6),
        c = [[Instr.cnot (⟨1, by omega⟩ : Fin 6) ⟨3, by omega⟩ (by decide),
              Instr.cnot (⟨2, by omega⟩ : Fin 6) ⟨4, by omega⟩ (by decide)]]
        ∧ (∀ Φ : QState 6, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨3, by omega⟩ = true
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨4, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨0, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨5, by omega⟩ = true) := by
  refine ⟨?_, ?_⟩
  · intro n N g hg
    refine ⟨[(List.finRange n).map (embGate g hg)], embU g, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact (embSpec g hg).1
    · exact (embSpec g hg).2.1
    · exact (embSpec g hg).2.2.1
    · exact (embSpec g hg).2.2.2.1
    · exact (embSpec g hg).2.2.2.2
  · have hginj : Function.Injective
        (fun v : Fin (2 + 2) => (⟨(v : ℕ) + 1, by omega⟩ : Fin 6)) := by
      intro a b h
      have h2 : (a : ℕ) + 1 = (b : ℕ) + 1 := congrArg Fin.val h
      exact Fin.ext (by omega)
    obtain ⟨hact, hhigh, hfix, hok, hd⟩ := embSpec
      (fun v : Fin (2 + 2) => (⟨(v : ℕ) + 1, by omega⟩ : Fin 6)) hginj
    refine ⟨[(List.finRange 2).map
        (embGate (fun v : Fin (2 + 2) => (⟨(v : ℕ) + 1, by omega⟩ : Fin 6)) hginj)],
      embU (fun v : Fin (2 + 2) => (⟨(v : ℕ) + 1, by omega⟩ : Fin 6)), ?_, hact, hok, hd,
      ?_, ?_, ?_, ?_⟩
    · rfl
    · refine Eq.trans (hhigh _ (⟨0, by omega⟩ : Fin 2)) ?_
      rfl
    · refine Eq.trans (hhigh _ (⟨1, by omega⟩ : Fin 2)) ?_
      rfl
    · refine Eq.trans (hfix _ (⟨0, by omega⟩ : Fin 6) ?_) ?_
      · intro j hj
        have h2 : (2 + (j : ℕ)) + 1 = 0 := congrArg Fin.val hj
        omega
      · rfl
    · refine Eq.trans (hfix _ (⟨5, by omega⟩ : Fin 6) ?_) ?_
      · intro j hj
        have hjlt : (j : ℕ) < 2 := j.isLt
        have h2 : (2 + (j : ℕ)) + 1 = 5 := congrArg Fin.val hj
        omega
      · rfl

