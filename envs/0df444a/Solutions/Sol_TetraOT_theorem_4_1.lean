-- Prove2me | solution 1 for TetraOT.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T05:16:23.335052+00:00
-- url     : https://prove2.me/submissions/f3bcfc26-e999-4e5f-828c-642abe7efc66

import Definitions.Def_TetraOT_tetrahedralRun
import Definitions.Def_TetraOT_PerfectSemiHonestRealizes
import Definitions.Def_TetraOT_idealROT

set_option autoImplicit false

namespace TetraOT

/-- Three ideal bits and an independent public message. -/
abbrev Seeds := (Bool × Bool × Bool) × Msg

/-- The ordered Alice hand determined by her output and the message. -/
def aliceHand : (Bool × Bool) → Msg → Fin 4 × Fin 4
  | (false, false), Msg.X => (1, 3)
  | (false, false), Msg.Y => (3, 2)
  | (false, false), Msg.Z => (2, 3)
  | (false, true), Msg.X => (2, 1)
  | (false, true), Msg.Y => (1, 2)
  | (false, true), Msg.Z => (3, 1)
  | (true, false), Msg.X => (3, 0)
  | (true, false), Msg.Y => (0, 3)
  | (true, false), Msg.Z => (2, 0)
  | (true, true), Msg.X => (0, 2)
  | (true, true), Msg.Y => (1, 0)
  | (true, true), Msg.Z => (0, 1)

/-- The Bob card determined by his output and the message. -/
def bobCard : (Bool × Bool) → Msg → Fin 4
  | (false, false), _ => 0
  | (false, true), Msg.X => 1
  | (false, true), Msg.Y => 2
  | (false, true), Msg.Z => 3
  | (true, false), Msg.X => 2
  | (true, false), Msg.Y => 1
  | (true, false), Msg.Z => 1
  | (true, true), Msg.X => 3
  | (true, true), Msg.Y => 3
  | (true, true), Msg.Z => 2

private theorem aliceHand_lookup :
    ∀ a b : Fin 4, a ≠ b →
      aliceHand (aliceTable a b).2 (aliceTable a b).1 = (a, b) := by
  decide

private theorem bobCard_lookup :
    ∀ (m : Msg) (c : Fin 4), bobCard (bobTable m c) m = c := by
  decide

private theorem raw_correctness :
    ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      (bobTable (aliceTable a b).1 c).2 =
        if (bobTable (aliceTable a b).1 c).1 then
          (aliceTable a b).2.2 else (aliceTable a b).2.1 := by
  decide

/-- Every one of the 24 actual deals returns Alice's selected bit. -/
theorem correctness (ρ : Equiv.Perm (Fin 4)) :
    (bobOut ρ).2 =
      if (bobOut ρ).1 then (aliceOut ρ).2 else (aliceOut ρ).1 := by
  exact raw_correctness (ρ 0) (ρ 1) (ρ 2)
    (ρ.injective.ne (by decide))
    (ρ.injective.ne (by decide))
    (ρ.injective.ne (by decide))

/-- Alice's view is reconstructed from her own output and the message. -/
theorem recover_viewA (ρ : Equiv.Perm (Fin 4)) :
    aliceHand (aliceOut ρ) (msg ρ) = viewA ρ := by
  exact aliceHand_lookup (ρ 0) (ρ 1) (ρ.injective.ne (by decide))

/-- Bob's view is reconstructed from his own output and the message. -/
theorem recover_viewB (ρ : Equiv.Perm (Fin 4)) :
    (bobCard (bobOut ρ) (msg ρ), msg ρ) = viewB ρ := by
  apply Prod.ext
  · exact bobCard_lookup (msg ρ) (ρ 2)
  · rfl

/-- Extract the three ideal bits and the message from a deal. -/
def encode (ρ : Equiv.Perm (Fin 4)) : Seeds :=
  (((aliceOut ρ).1, (aliceOut ρ).2, (bobOut ρ).1), msg ρ)

private def rawEncode (f : Fin 4 → Fin 4) : Seeds :=
  (((aliceTable (f 0) (f 1)).2.1, (aliceTable (f 0) (f 1)).2.2,
    (bobTable (aliceTable (f 0) (f 1)).1 (f 2)).1),
    (aliceTable (f 0) (f 1)).1)

private def decodeFun : Seeds → Fin 4 → Fin 4
  | ((false, false, false), Msg.X) => ![1, 3, 0, 2]
  | ((false, false, false), Msg.Y) => ![3, 2, 0, 1]
  | ((false, false, false), Msg.Z) => ![2, 3, 0, 1]
  | ((false, false, true), Msg.X) => ![1, 3, 2, 0]
  | ((false, false, true), Msg.Y) => ![3, 2, 1, 0]
  | ((false, false, true), Msg.Z) => ![2, 3, 1, 0]
  | ((false, true, false), Msg.X) => ![2, 1, 0, 3]
  | ((false, true, false), Msg.Y) => ![1, 2, 0, 3]
  | ((false, true, false), Msg.Z) => ![3, 1, 0, 2]
  | ((false, true, true), Msg.X) => ![2, 1, 3, 0]
  | ((false, true, true), Msg.Y) => ![1, 2, 3, 0]
  | ((false, true, true), Msg.Z) => ![3, 1, 2, 0]
  | ((true, false, false), Msg.X) => ![3, 0, 1, 2]
  | ((true, false, false), Msg.Y) => ![0, 3, 2, 1]
  | ((true, false, false), Msg.Z) => ![2, 0, 3, 1]
  | ((true, false, true), Msg.X) => ![3, 0, 2, 1]
  | ((true, false, true), Msg.Y) => ![0, 3, 1, 2]
  | ((true, false, true), Msg.Z) => ![2, 0, 1, 3]
  | ((true, true, false), Msg.X) => ![0, 2, 1, 3]
  | ((true, true, false), Msg.Y) => ![1, 0, 2, 3]
  | ((true, true, false), Msg.Z) => ![0, 1, 3, 2]
  | ((true, true, true), Msg.X) => ![0, 2, 3, 1]
  | ((true, true, true), Msg.Y) => ![1, 0, 3, 2]
  | ((true, true, true), Msg.Z) => ![0, 1, 2, 3]

private def decodeInvFun (s : Seeds) (i : Fin 4) : Fin 4 :=
  if decodeFun s 0 = i then 0
  else if decodeFun s 1 = i then 1
  else if decodeFun s 2 = i then 2
  else 3

private theorem decode_left_inverse :
    ∀ (s : Seeds) (i : Fin 4), decodeInvFun s (decodeFun s i) = i := by
  decide

private theorem decode_right_inverse :
    ∀ (s : Seeds) (i : Fin 4), decodeFun s (decodeInvFun s i) = i := by
  decide

/-- The unique actual deal corresponding to any choice of ideal bits and message. -/
def decode (s : Seeds) : Equiv.Perm (Fin 4) where
  toFun := decodeFun s
  invFun := decodeInvFun s
  left_inv := decode_left_inverse s
  right_inv := decode_right_inverse s

private theorem rawEncode_decodeFun :
    ∀ s : Seeds, rawEncode (decodeFun s) = s := by
  decide

@[simp] theorem encode_decode (s : Seeds) : encode (decode s) = s := by
  exact rawEncode_decodeFun s

theorem encode_bijective : Function.Bijective encode := by
  apply (Fintype.bijective_iff_surjective_and_card encode).2
  refine ⟨fun s => ⟨decode s, encode_decode s⟩, ?_⟩
  have h : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    decide
  exact h.trans (by decide)

@[simp] theorem decode_encode (ρ : Equiv.Perm (Fin 4)) : decode (encode ρ) = ρ := by
  apply encode_bijective.1
  exact encode_decode (encode ρ)

/-- A bijection between the 24 deals and three independent bits plus a message. -/
def dealEquiv : Equiv.Perm (Fin 4) ≃ Seeds where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

@[simp] theorem dealEquiv_apply (ρ : Equiv.Perm (Fin 4)) : dealEquiv ρ = encode ρ := rfl

end TetraOT

set_option autoImplicit false

noncomputable section

namespace TetraOT

universe u v w x y z s

/-- Uniform finite distributions are invariant under an equivalence. -/
theorem map_uniform_equiv {α : Type u} {β : Type v}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  have h : ∀ a : α, b = e a ↔ a = e.symm b := by
    intro a
    constructor
    · intro hab
      exact e.injective (hab.symm.trans (e.apply_symm_apply b).symm)
    · intro hab
      rw [hab, e.apply_symm_apply]
  simp_rw [h]
  rw [tsum_ite_eq]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- A deterministic calculation may be performed after changing uniform coordinates. -/
theorem map_uniform_equiv_comp {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (f : β → γ) :
    (PMF.uniformOfFintype α).map (fun a => f (e a)) =
      (PMF.uniformOfFintype β).map f := by
  calc
    (PMF.uniformOfFintype α).map (fun a => f (e a)) =
        ((PMF.uniformOfFintype α).map e).map f := by
      simpa only [Function.comp_def] using
        (PMF.map_comp e (PMF.uniformOfFintype α) f).symm
    _ = (PMF.uniformOfFintype β).map f := by rw [map_uniform_equiv e]

/-- A uniform point of a finite product consists of two independent uniform points. -/
theorem uniform_prod_bind {α : Type u} {β : Type v}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind
        (fun a => (PMF.uniformOfFintype β).map (Prod.mk a)) := by
  classical
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.uniformOfFintype_apply, PMF.bind_apply]
  have hm : ∀ a' : α,
      ((PMF.uniformOfFintype β).map (Prod.mk a')) (a, b) =
        if a' = a then (Fintype.card β : ENNReal)⁻¹ else 0 := by
    intro a'
    by_cases ha : a' = a
    · subst a'
      simp [PMF.map_apply, PMF.uniformOfFintype_apply]
    · simp [PMF.map_apply, ha, Ne.symm ha]
  simp_rw [hm, mul_ite, mul_zero]
  rw [tsum_ite_eq, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))

/-- Discarding the independent second coordinate preserves the uniform first-coordinate law. -/
theorem uniform_map_fst {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α → γ) :
    (PMF.uniformOfFintype (α × β)).map (fun p => f p.1) =
      (PMF.uniformOfFintype α).map f := by
  rw [uniform_prod_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (PMF.uniformOfFintype α).bind
      (fun a => (PMF.uniformOfFintype β).map (Function.const β (f a))) = _
  simp only [PMF.map_const]
  rfl

/-- An independent uniform coordinate can be sampled after observing a function of the first
coordinate. The equality retains that observed value jointly with the simulated view. -/
theorem uniform_product_map_pair {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → γ) (g : γ → β → δ) :
    (PMF.uniformOfFintype (α × β)).map (fun p => (g (f p.1) p.2, f p.1)) =
      ((PMF.uniformOfFintype α).map f).bind
        (fun c => (PMF.uniformOfFintype β).map (fun b => (g c b, c))) := by
  rw [uniform_prod_bind, PMF.map_bind, PMF.bind_map]
  simp only [PMF.map_comp, Function.comp_def]

/-- A finite uniform protocol is perfectly semi-honest secure when its randomness is equivalent
to independent ideal coins and a uniform message, and each view can be recovered from only its
own output and that message. Both simulated distributions retain both parties' outputs. -/
theorem uniform_realizes_by_equiv
    {Ω : Type u} {R : Type v} {M : Type w}
    {OA : Type x} {OB : Type y} {VA : Type z} {VB : Type s}
    [Fintype Ω] [Nonempty Ω] [Fintype R] [Nonempty R] [Fintype M] [Nonempty M]
    (e : Ω ≃ R × M) (ideal : R → OA × OB)
    (viewA : Ω → VA) (viewB : Ω → VB) (outA : Ω → OA) (outB : Ω → OB)
    (decodeA : OA → M → VA) (decodeB : OB → M → VB)
    (hout : ∀ ω, (outA ω, outB ω) = ideal (e ω).1)
    (hA : ∀ ω, viewA ω = decodeA (outA ω) (e ω).2)
    (hB : ∀ ω, viewB ω = decodeB (outB ω) (e ω).2) :
    PerfectSemiHonestRealizes (PMF.uniformOfFintype Ω)
      viewA viewB outA outB ((PMF.uniformOfFintype R).map ideal) := by
  unfold PerfectSemiHonestRealizes
  refine ⟨?_, ⟨fun o => (PMF.uniformOfFintype M).map (decodeA o), ?_⟩,
    ⟨fun o => (PMF.uniformOfFintype M).map (decodeB o), ?_⟩⟩
  · calc
      (PMF.uniformOfFintype Ω).map (fun ω => (outA ω, outB ω)) =
          (PMF.uniformOfFintype Ω).map (fun ω => ideal (e ω).1) := by
        exact congrArg (fun f : Ω → OA × OB => (PMF.uniformOfFintype Ω).map f)
          (funext hout)
      _ = (PMF.uniformOfFintype (R × M)).map (fun p => ideal p.1) :=
        map_uniform_equiv_comp e (fun p => ideal p.1)
      _ = (PMF.uniformOfFintype R).map ideal := uniform_map_fst ideal
  · calc
      (PMF.uniformOfFintype Ω).map (fun ω => (viewA ω, outA ω, outB ω)) =
          (PMF.uniformOfFintype Ω).map
            (fun ω => (decodeA (ideal (e ω).1).1 (e ω).2, ideal (e ω).1)) := by
        apply congrArg (fun f : Ω → VA × OA × OB => (PMF.uniformOfFintype Ω).map f)
        funext ω
        rw [← hout ω, hA ω]
      _ = (PMF.uniformOfFintype (R × M)).map
          (fun p => (decodeA (ideal p.1).1 p.2, ideal p.1)) :=
        map_uniform_equiv_comp e (fun p => (decodeA (ideal p.1).1 p.2, ideal p.1))
      _ = ((PMF.uniformOfFintype R).map ideal).bind
          (fun o => (PMF.uniformOfFintype M).map (fun m => (decodeA o.1 m, o))) :=
        uniform_product_map_pair ideal (fun o m => decodeA o.1 m)
      _ = ((PMF.uniformOfFintype R).map ideal).bind
          (fun o => ((PMF.uniformOfFintype M).map (decodeA o.1)).map
            (fun v => (v, o.1, o.2))) := by
        simp only [PMF.map_comp, Function.comp_def]
  · calc
      (PMF.uniformOfFintype Ω).map (fun ω => (viewB ω, outA ω, outB ω)) =
          (PMF.uniformOfFintype Ω).map
            (fun ω => (decodeB (ideal (e ω).1).2 (e ω).2, ideal (e ω).1)) := by
        apply congrArg (fun f : Ω → VB × OA × OB => (PMF.uniformOfFintype Ω).map f)
        funext ω
        rw [← hout ω, hB ω]
      _ = (PMF.uniformOfFintype (R × M)).map
          (fun p => (decodeB (ideal p.1).2 p.2, ideal p.1)) :=
        map_uniform_equiv_comp e (fun p => (decodeB (ideal p.1).2 p.2, ideal p.1))
      _ = ((PMF.uniformOfFintype R).map ideal).bind
          (fun o => (PMF.uniformOfFintype M).map (fun m => (decodeB o.2 m, o))) :=
        uniform_product_map_pair ideal (fun o m => decodeB o.2 m)
      _ = ((PMF.uniformOfFintype R).map ideal).bind
          (fun o => ((PMF.uniformOfFintype M).map (decodeB o.2)).map
            (fun v => (v, o.1, o.2))) := by
        simp only [PMF.map_comp, Function.comp_def]

end TetraOT

set_option autoImplicit false

theorem solution :
    TetraOT.PerfectSemiHonestRealizes
      TetraOT.deal TetraOT.viewA TetraOT.viewB
      TetraOT.aliceOut TetraOT.bobOut TetraOT.idealROT := by
  let : Nonempty TetraOT.Msg := ⟨TetraOT.Msg.X⟩
  apply TetraOT.uniform_realizes_by_equiv
    TetraOT.dealEquiv
    (fun x : Bool × Bool × Bool =>
      ((x.1, x.2.1), (x.2.2, if x.2.2 then x.2.1 else x.1)))
    TetraOT.viewA TetraOT.viewB TetraOT.aliceOut TetraOT.bobOut
    TetraOT.aliceHand (fun o m => (TetraOT.bobCard o m, m))
  · intro ρ
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact TetraOT.correctness ρ
  · intro ρ
    exact (TetraOT.recover_viewA ρ).symm
  · intro ρ
    exact (TetraOT.recover_viewB ρ).symm
