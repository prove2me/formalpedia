-- Prove2me | solution 1 for VWZClique.count_large_cliques
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:08:32.747181+00:00
-- url     : https://prove2.me/submissions/2675d320-8f65-4f0a-8229-442a80c6463e

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_NativeCliqueCompiler
import Definitions.Def_VWZClique_NativeProjectionContract
import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Theorems.Thm_VWZClique_IntegerRAM_NativeArena_wordRam_of_projected_kernel
import Theorems.Thm_VWZClique_IntegerRAM_Projected_Dense_all_runs
import Theorems.Thm_VWZClique_IntegerRAM_Projected_Large_from_dense
import Theorems.Thm_VWZClique_IntegerRAM_Projected_Preparation_run

/- DyadicBounds -/
section
open VWZClique
namespace VWZClique.RankSwap

theorem denominator_bits {L : ℕ} (j : BasisLabel L) : denominatorExponent j ≤ L := by
  simpa [denominatorExponent] using Finset.card_le_univ (Finset.univ.filter (fun i => ¬j i < 2))

end VWZClique.RankSwap
end

/- WeightedAlgebra -/
section
open VWZClique
namespace VWZClique.WeightedProof

abbrev KernelArgs (L : ℕ) := PairBits L × PairBits L × PairBits L × PairBits L

noncomputable def evaluate {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (w : ChannelKey L → F) : (KernelArgs L → F) →ₗ[F] F where
  toFun k :=
    ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
      ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
        k (x,x',y,y') * placedChannel E w 0 (block x z₁) (block y z₂) *
          placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum,mul_assoc]

def pairKernel {F : Type*} [Field F] {L : ℕ} (p q : PairBits L → PairBits L → F) :
    KernelArgs L → F := fun z => p z.1 z.2.1 * q z.2.2.1 z.2.2.2

private theorem evalMask {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    evaluate E w (pairKernel (maskKernel a) (maskKernel b)) = placedFold E a b w := by
  rfl

private theorem evalProjection {F : Type*} [Field F] [CharZero F] {L : ℕ} (E : Finset EdgeSlot)
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → F) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    evaluate E w (pairKernel (projected Λ d) (projected Λ d)) = doubleProjection Λ Λ d d w := by
  unfold doubleProjection
  simp_rw [hc]
  rfl

theorem decomposition {F : Type*} [Field F] [CharZero F] {L M : ℕ}
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ)
    (m : Fin M → Mask L) (c : Fin M → ℤ)
    (hdecomp : ∀ x y : PairBits L,
      (if x = y then (1 : ℚ) else 0) =
        (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
        ∑ i, (c i : ℚ) * swapEntry (m i) x y)
    (E : Finset EdgeSlot) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w =
      doubleProjection Λ Λ (fun j => (d j : F)) (fun j => (d j : F)) w +
      (∑ i, (c i : F) * placedFold E (some (m i)) none w) +
      (∑ j, (c j : F) * placedFold E none (some (m j)) w) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) * placedFold E (some (m i)) (some (m j)) w := by
  classical
  let I := maskKernel (F := F) (L := L) none
  let R := projected Λ (fun j => (d j : F))
  let S := fun i => maskKernel (F := F) (some (m i))
  have hkernel (x y : PairBits L) : I x y = R x y + ∑ i, (c i : F) * S i x y := by
    have eqn := congrArg (fun q : ℚ => (q : F)) (hdecomp x y)
    simpa [I,R,S,maskKernel,projected,swapEntry,apply_ite] using eqn
  have hp : pairKernel I I = pairKernel R R +
      (∑ i, (c i : F) • pairKernel (S i) I) +
      (∑ j, (c j : F) • pairKernel I (S j)) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) • pairKernel (S i) (S j) := by
    funext z
    rcases z with ⟨x,x',y,y'⟩
    simp only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairKernel]
    simp only [← mul_assoc, ← Finset.sum_mul]
    have swap (j : Fin M) : (c j : F) * I x x' * S j y y' = I x x' * ((c j : F) * S j y y') := by ring
    have both (i j : Fin M) : (c i : F) * (c j : F) * S i x x' * S j y y' =
        ((c i : F) * S i x x') * ((c j : F) * S j y y') := by ring
    simp_rw [swap,both,← Finset.mul_sum,← Finset.sum_mul]
    rw [hkernel x x',hkernel y y']
    ring
  have he := congrArg (evaluate E w) hp
  simpa [I,R,S,map_sum,evalMask,evalProjection E Λ _ w hc] using he

end VWZClique.WeightedProof
end

/- UniformExpansion -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

attribute [instance] Expansion.finite

theorem windowExpansion_coefficients (K L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(((windowExpansion K L).coefficients i : ℤ) : ℝ)| ≤
      2^(lower K L)*4^(width K L)) ∧
    ∀ j : BasisLabel L, ∃ q : ℕ, q≤L ∧ ∃ z : ℤ,
      |(z:ℝ)| ≤ 1 + 3^L * (2^(lower K L)*4^(width K L)) ∧
      (windowExpansion K L).diagonal j = (z:ℚ)/2^q := by
  have hh := (Window.correct (lower K L) (width K L)).2.1
  exact ⟨fun i => term_bound hh i,fun j => ⟨denominatorExponent j,denominator_bits j,_,
    residual_bound (by positivity) hh j,rfl⟩⟩

theorem Expansion.decompose {L : ℕ} (q : Expansion L) (E : Finset EdgeSlot) (w : ChannelKey L → ℚ)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w = doubleProjection q.labels q.labels q.diagonal q.diagonal w +
      (∑ i, (q.coefficients i : ℚ)*placedFold E (some (q.masks i)) none w) +
      (∑ j, (q.coefficients j : ℚ)*placedFold E none (some (q.masks j)) w) -
      ∑ i, ∑ j, ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*
        placedFold E (some (q.masks i)) (some (q.masks j)) w := by
  classical
  let e := (Fintype.equivFin q.Index).symm
  have hdecomp (x y : PairBits L) := q.identity x y
  have hx (x y : PairBits L) :
      (if x=y then (1:ℚ) else 0) =
        (∑ j ∈ q.labels, q.diagonal j * basisEntry j x * basisEntry j y) +
        ∑ i, (q.coefficients (e i) : ℚ)*swapEntry (q.masks (e i)) x y := by
    rw [e.sum_comp (fun i => (q.coefficients i : ℚ)*swapEntry (q.masks i) x y)]
    exact hdecomp x y
  have h := decomposition q.labels q.diagonal (fun i => q.masks (e i)) (fun i => q.coefficients (e i)) hx E w hc
  rw [e.sum_comp (fun i => (q.coefficients i : ℚ) * placedFold E (some (q.masks i)) none w),
    e.sum_comp (fun j => (q.coefficients j : ℚ) * placedFold E none (some (q.masks j)) w)] at h
  let f := fun i j => ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*placedFold E (some (q.masks i)) (some (q.masks j)) w
  have h₂ : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
    simp_rw [fun i => e.sum_comp (f (e i))]
    exact e.sum_comp (fun i => ∑ j,f i j)
  rw [h₂] at h
  simpa only [f,Rat.cast_id] using h

end VWZClique.UniformFolds
end

/- FoldKernel -/
section
open VWZClique
namespace VWZClique.FoldProof

def post {L : ℕ} (m : Option (Mask L)) (x : PairBits L) : PairBits L :=
  match m with
  | none => x
  | some mask => (restore mask (fun r => r.2.2.1) x.2, restore mask (fun r => r.2.2.2) x.1)

theorem support {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ pin (some m) Prod.fst x.1 ∧ pin (some m) (fun r => r.2.1) x.2 ∧
      y = post (some m) x := by
  constructor
  · intro h
    have fixed (i : Fin L) (r : Quad) (hi : m i = some r) := h i
    refine ⟨?_,?_,?_⟩
    · intro i r hr
      have hh := h i
      rcases r with ⟨s,u,v,t⟩
      simpa [hr] using congrArg Prod.fst (show (x.1 i,x.2 i,y.1 i,y.2 i) = (s,u,v,t) by simpa [hr] using hh)
    · intro i r hr
      rcases r with ⟨s,u,v,t⟩
      have hh := h i
      simp [hr] at hh
      exact hh.2.1
    · apply Prod.ext <;> funext i <;> have hh := h i <;>
        cases hm : m i with
        | none => simp [hm] at hh; simp [post,restore,hm]; grind
        | some r => rcases r with ⟨s,u,v,t⟩; simp [hm] at hh; simp [post,restore,hm]; grind
  · rintro ⟨h₁,h₂,rfl⟩ i
    cases h : m i with
    | none => simp [post,restore,h]
    | some r =>
      obtain ⟨s,u,v,t⟩ := r
      simp [post,restore,h,h₁ i _ h,h₂ i _ h]

theorem kernel_eq {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (x y : PairBits L) :
    maskKernel (F := F) m x y = if y = post m x then
      flag m Prod.fst x.1 * flag m (fun r => r.2.1) x.2 else 0 := by
  classical
  cases m with
  | none => simp [post,maskKernel,flag,pin,eq_comm]
  | some m =>
    simp only [maskKernel,support,flag]
    split_ifs <;> simp_all

theorem sum_kernels {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (f : PairBits L → PairBits L → PairBits L → PairBits L → F) :
    (∑ x, ∑ x', ∑ y, ∑ y', maskKernel a x x' * maskKernel b y y' * f x x' y y') =
    ∑ x, ∑ y, ((flag a Prod.fst x.1 * flag a (fun r => r.2.1) x.2) *
      (flag b Prod.fst y.1 * flag b (fun r => r.2.1) y.2)) * f x (post a x) y (post b y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp [kernel_eq, mul_ite, ite_mul]

end VWZClique.FoldProof
end

/- FoldRouting -/
section
open VWZClique
namespace VWZClique.FoldProof

def slotWord {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) (h : Fin 3) (i : Slot) : Bits L :=
  (route a b h i).2 (X (route a b h i).1)

abbrev Packed (L : ℕ) := Bits L × Bits L × Block L × PairBits L × PairBits L

def unpack {L : ℕ} (z : Packed L) : V → Bits L := fun v =>
  let p := (finProdFinEquiv (m := 3) (n := 3)).symm v
  (![block z.2.2.2.1 z.1, block z.2.2.2.2 z.2.1, z.2.2.1] p.1) p.2

@[simp] theorem unpack_site {L : ℕ} (z : Packed L) (g i : Fin 3) :
    unpack z (site g i) = (![block z.2.2.2.1 z.1,block z.2.2.2.2 z.2.1,z.2.2.1] g) i := by
  simp only [unpack,site,Equiv.symm_apply_apply]

def packEquiv (L : ℕ) : (V → Bits L) ≃ Packed L where
  toFun X := (X (site 0 2),X (site 1 2),fun i => X (site 2 i),
    (X (site 0 0),X (site 0 1)),(X (site 1 0),X (site 1 1)))
  invFun := unpack
  left_inv := by
    intro X
    funext v
    obtain ⟨⟨g,i⟩,rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective v
    fin_cases g <;> fin_cases i <;> rfl
  right_inv := by
    rintro ⟨z₁,z₂,c,x,y⟩
    simp [block, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem routed_slots {L : ℕ} (a b : Option (Mask L)) (z₁ z₂ : Bits L) (c : Block L)
    (x y : PairBits L) (h : Fin 3) (s : Slot) :
    slotWord a b (unpack (z₁,z₂,c,x,y)) h s =
    Sum.elim (![block x z₁,block (post b y) z₂,c] h)
      (![block y z₂,c,block (post a x) z₁] h) s := by
  cases s with
  | inl i => fin_cases h <;> fin_cases i <;> cases b <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]
  | inr i => fin_cases h <;> fin_cases i <;> cases a <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]

noncomputable def unary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (v : Fin 3 × Slot) : F :=
  w (v.1,.inl (v.2,slotWord a b X v.1 v.2))

noncomputable def binary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (e : EdgeSlot) : F :=
  w (e.1,.inr (e.2.1,e.2.2,slotWord a b X e.1 e.2.1,slotWord a b X e.1 e.2.2))

theorem channels_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (z₁ z₂ : Bits L) (c : Block L) (x y : PairBits L) (w : ChannelKey L → F) :
    let X := unpack (z₁,z₂,c,x,y)
    placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block (post b y) z₂) c *
    placedChannel E w 2 c (block (post a x) z₁) =
    (∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e := by
  classical
  let X := unpack (z₁,z₂,c,x,y)
  let row := ![block x z₁,block (post b y) z₂,c]
  let col := ![block y z₂,c,block (post a x) z₁]
  have chan (h : Fin 3) : placedChannel E w h (row h) (col h) =
      (∏ s : Slot, unary a b X w (h,s)) * ∏ e ∈ E, if e.1=h then binary a b X w e else 1 := by
    unfold placedChannel unary binary
    dsimp only
    apply congrArg₂ (·*·)
    · simp only [X,row,col,routed_slots]
    · apply Finset.prod_congr rfl
      intro e he
      by_cases hh : e.1=h
      · subst h
        simp [X,row,col,routed_slots]
      · simp [hh]
  have allRows := Finset.prod_congr (s₁ := Finset.univ) rfl (fun h _ => chan h)
  rw [Finset.prod_mul_distrib] at allRows
  rw [Finset.prod_comm (f := fun h e => if e.1=h then binary a b X w e else 1)] at allRows
  simp only [Finset.prod_ite_eq,Finset.mem_univ,if_true] at allRows
  dsimp only
  rw [Fintype.prod_prod_type]
  convert! allRows using 1
  rw [Fin.prod_univ_three]
  rfl

noncomputable def checks {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) : F :=
  (flag a Prod.fst (X (site 0 0)) * flag a (fun r => r.2.1) (X (site 0 1))) *
  (flag b Prod.fst (X (site 1 0)) * flag b (fun r => r.2.1) (X (site 1 1)))

private theorem five_sums {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid F] (f : A × B × C × D × E → F) :
    ∑ z, f z = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f (a,b,c,d,e) := by simp only [Fintype.sum_prod_type]

theorem reindexed {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    placedFold E a b w = ∑ X : V → Bits L, checks a b X *
      ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  classical
  let expr := fun X : V → Bits L => checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e)
  rw [← (packEquiv L).symm.sum_comp expr]
  rw [five_sums (D := PairBits L) (E := PairBits L)]
  unfold placedFold
  apply Finset.sum_congr rfl
  intro z₁ _
  apply Finset.sum_congr rfl
  intro z₂ _
  apply Finset.sum_congr rfl
  intro c _
  let f := fun x x' y y' => placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  have h := sum_kernels a b f
  dsimp only [f] at h
  simp only [mul_assoc] at h ⊢
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc := channels_product a b E z₁ z₂ c x y w
  dsimp only at hc
  change _ = expr (unpack (z₁,z₂,c,x,y))
  unfold expr
  rw [← hc]
  simp [checks,block,mul_assoc,Fin.isValue]

end VWZClique.FoldProof
end

/- CircuitBuild -/
section
open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Circuit

/-- Extend any straight-line program, retaining all previous values. -/
def Build {F I : Type*} [Field F] (f : (I → F) → F) (b : ℕ) : Prop :=
  ∀ (r : ℕ) (p : Program F I r), ∃ (n : ℕ) (q : Program F I n) (out : Fin n) (old : Fin r → Fin n),
    q.cost ≤ p.cost + b ∧ (∀ w, q.eval w out = f w) ∧ ∀ w i, q.eval w (old i) = p.eval w i

variable {F I : Type*} [Field F]

theorem const (c : F) : Build (fun _ : I → F => c) 0 := by
  intro r p
  exact ⟨r+1,.step p (.constant c),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem read (i : I) : Build (fun w : I → F => w i) 0 := by
  intro r p
  exact ⟨r+1,.step p (.input i),0,Fin.succ,by simp [Program.cost,Gate.cost],fun _ => rfl,fun _ _ => rfl⟩

theorem binary {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b)
    (fn : F → F → F) (gate : ∀ {n : ℕ}, Fin n → Fin n → Gate F I (Fin n))
    (cost : ∀ {n : ℕ} (i j : Fin n), (gate i j).cost ≤ 1)
    (eval : ∀ {n : ℕ} (w : I → F) (v : Fin n → F) i j, (gate i j).eval w v = fn (v i) (v j)) :
    Build (fun w => fn (f w) (g w)) (a+b+1) := by
  intro r p
  obtain ⟨r₁,p₁,o₁,old₁,h₁,e₁,l₁⟩ := hf r p
  obtain ⟨r₂,p₂,o₂,old₂,h₂,e₂,l₂⟩ := hg r₁ p₁
  let g' := gate (old₂ o₁) o₂
  refine ⟨r₂+1,.step p₂ g',0,fun i => (old₂ (old₁ i)).succ,?_,?_,?_⟩
  · have hc := cost (old₂ o₁) o₂
    change p₂.cost + (gate (old₂ o₁) o₂).cost ≤ _
    omega
  · intro w
    change (gate _ _).eval _ _ = _
    rw [eval,l₂,e₁,e₂]
  · intro w i
    exact (l₂ w _).trans (l₁ w _)

theorem add {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w + g w) (a+b+1) :=
  binary hf hg (·+·) Gate.add (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem mul {f g : (I → F) → F} {a b : ℕ} (hf : Build f a) (hg : Build g b) :
    Build (fun w => f w * g w) (a+b+1) :=
  binary hf hg (·*·) Gate.mul (fun _ _ => le_rfl) (fun _ _ _ _ => rfl)

theorem sum {J : Type*} (s : Finset J) (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j ∈ s, Build (f j) b) :
    Build (fun w => ∑ j ∈ s, f j w) (s.card * (b+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (I := I) (0:F))
  | @insert j s hj ih =>
    have h' := add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [hj,Finset.card_insert_of_notMem, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

end VWZClique.Circuit
end

/- GraphWeights -/
section
open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.FoldProof

/-- Compute every member of a finite table, retaining its output register. -/
theorem tabulate {F I J : Type*} [Field F] [Fintype J] (f : J → (I → F) → F) (b : ℕ)
    (h : ∀ j, Circuit.Build (f j) b) :
    ∃ (r : ℕ) (p : Program F I r) (out : J → Fin r),
      p.cost ≤ Fintype.card J * b ∧ ∀ w j, p.eval w (out j) = f j w := by
  classical
  have part (s : Finset J) : ∃ (r : ℕ) (p : Program F I r) (out : (j:J) → j ∈ s → Fin r),
      p.cost ≤ s.card*b ∧ ∀ w j hj, p.eval w (out j hj) = f j w := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨0,.nil,fun _ h => False.elim (by simp at h),by simp [Program.cost],fun _ _ h => False.elim (by simp at h)⟩
    | @insert j s hj ih =>
      obtain ⟨n,p,out,hc,he⟩ := ih
      obtain ⟨r,q,o,old,hc',ho,hold⟩ := h j n p
      refine ⟨r,q,fun i hi => if h : i=j then o else old (out i (by simpa [h] using hi)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hj,Nat.succ_mul]
        omega
      · intro w i hi
        by_cases hij : i=j
        · subst i; simpa using ho w
        · simpa [hij,hold] using he w i (by simpa [hij] using hi)
  obtain ⟨r,p,out,hc,he⟩ := part Finset.univ
  exact ⟨r,p,fun j => out j (Finset.mem_univ _),hc,fun w j => he w j _⟩

def weightAt {n : ℕ} (x : V → Fin n) : Kind → WeightKey n
  | .inl i => .inl (i,x i)
  | .inr (i,j) => .inr (i,j,x i,x j)

theorem value_at_ends {n : ℕ} (x : V → Fin n) (p : V × V) :
    addressValue (weightAt x (kind p)) p.1 = x p.1 ∧
    addressValue (weightAt x (kind p)) p.2 = x p.2 := by
  obtain ⟨i,j⟩ := p
  by_cases h : i=j
  · subst j; simp [kind,weightAt,addressValue]
  · by_cases h' : i < j <;> simp [kind,weightAt,addressValue,h,h',Ne.symm h]

theorem oriented (p : V × V) (i j : V) (h : kind p = .inr (i,j)) :
    i < j ∧ (p = (i,j) ∨ p = (j,i)) := by
  obtain ⟨u,v⟩ := p
  by_cases huv : u=v
  · simp [kind,huv] at h
  · by_cases hlt : u<v
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨hlt,Or.inl rfl⟩
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm huv),Or.inr rfl⟩

end VWZClique.FoldProof
end

/- FoldFactors -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem token_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (X : V → Bits L) (w : ChannelKey L → F) :
    (∏ v : FoldToken E, weight a b v (X (ends a b v).1) (X (ends a b v).2) w) =
    checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  congr 1
  · rw [Fin.prod_univ_four]
    change ((flag a _ _ * flag a _ _) * flag b _ _) * flag b _ _ = _
    simp only [checks,mul_assoc]
    rfl
  · congr 1
    change (∏ e : ↥E, binary a b X w e.val) = _
    exact Finset.prod_attach E (binary a b X w)

end VWZClique.FoldProof
end

/- FoldEdges -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem folded_adj {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (e : EdgeSlot) (he : e ∈ E) (hne : (epPair a b e).1 ≠ (epPair a b e).2) :
    (foldedGraph a b E).Adj (epPair a b e).1 (epPair a b e).2 :=
  ⟨Finset.mem_image_of_mem (edgeImage a b) he, hne⟩

end VWZClique.FoldProof
end

/- WeightedPlacement -/
section
open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

def ends (e : EdgeSlot) : V × V := (endpoint e.1 e.2.1, endpoint e.1 e.2.2)

theorem locate_ends : ∀ u v : V, ends (locate u v) = (u,v) := by decide

theorem chosen_ends (π : Equiv.Perm V) (p : V × V) :
    ends (chosen π p) = (π.symm p.1,π.symm p.2) ∨
      ends (chosen π p) = (π.symm p.2,π.symm p.1) := by
  by_cases h : π.symm p.1 ≤ π.symm p.2
  · simp [chosen,locate_ends,min_eq_left h,max_eq_right h]
  · simp [chosen,locate_ends,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]

theorem chosen_inj (π : Equiv.Perm V) (H : SimpleGraph V) : Set.InjOn (chosen π) (↑(pairs H)) := by
  classical
  intro p hp q hq he
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hq' := (Finset.mem_filter.mp hq).2.1
  have hinv (a b : V) : π.symm a = π.symm b ↔ a=b := π.symm.injective.eq_iff
  have h := congrArg ends he
  rcases chosen_ends π p with p1|p2 <;> rcases chosen_ends π q with q1|q2 <;>
    simp_all [Prod.ext_iff] <;> exact (lt_asymm hq' hp').elim

end VWZClique.WeightedProof
end

/- WeightedChannels -/
section
open VWZClique VWZClique.FoldProof
namespace VWZClique.WeightedProof

noncomputable def indexWord (L : ℕ) : Bits L ≃ Fin (2^L) :=
  Fintype.equivOfCardEq (by simp [Bits])

noncomputable def channelTag {F : Type*} [Field F] {L : ℕ}
    (π : Equiv.Perm V) (E : Finset EdgeSlot) : ChannelKey L → WeightKey (2^L) ⊕ F
  | (h,.inl (.inl i,x)) => .inl (.inl (π (site h i), indexWord L x))
  | (_,.inl (.inr _,_)) => .inr 1
  | (h,.inr (s,t,x,y)) => if (h,s,t) ∈ E then
      .inl (edgeKey (π (endpoint h s)) (π (endpoint h t)) (indexWord L x) (indexWord L y))
    else .inr 1

theorem supported {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (h : Fin 3) (a b : Block L) :
    let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
    channel inputs h a b = placedChannel E inputs h a b := by
  classical
  dsimp only
  unfold channel placedChannel
  dsimp only
  apply congrArg (fun y : F => _ * y)
  let x := Sum.elim a b
  let v := fun e : EdgeSlot => if e.1=h then literal w
    (channelTag π E (h,.inr (e.2.1,e.2.2,x e.2.1,x e.2.2))) else 1
  have addBack : (∏ e ∈ E, v e) = ∏ e : EdgeSlot, v e := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    by_cases h' : e.1=h
    · obtain ⟨k,s,t⟩ := e
      dsimp only at h'
      subst k
      simp [v,channelTag,he,literal]
    · simp [v,h']
  change _ = ∏ e ∈ E, v e
  rw [addBack,Fintype.prod_prod_type,Finset.prod_comm (f := fun k st => v (k,st))]
  simp only [v,Finset.prod_ite_eq',Finset.mem_univ,if_true]
  rw [Fintype.prod_prod_type]

theorem no_swap_word {L : ℕ} (X : V → Bits L) (h : Fin 3) (s : Slot) :
    slotWord none none X h s = X (endpoint h s) := by
  cases s with
  | inl i => fin_cases h <;> rfl
  | inr i => fin_cases h <;> rfl

theorem encode_graph {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (channelTag π (slots π H) j)) =
      weightedSum H w := by
  classical
  let E := slots π H
  let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
  let perm := π.arrowCongr (indexWord L)
  rw [reindexed,weightedSum,← perm.sum_comp]
  apply Finset.sum_congr rfl
  intro X _
  let X' := perm X
  have mapped (v : V) : X' (π v) = indexWord L (X v) := by simp [X',perm,Equiv.arrowCongr_apply]
  have mapped' (v : V) : indexWord L (X (π.symm v)) = X' v := rfl
  have uv : (∏ v : Fin 3 × Slot, unary none none X inputs v) =
      ∏ i : V, w (.inl (i,X' i)) := by
    let u := fun i : V => w (Sum.inl (i,X' i))
    rw [← Equiv.prod_comp π u, ← (finProdFinEquiv (m:=3) (n:=3)).prod_comp (fun i => u (π i))]
    rw [Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    rw [Fintype.prod_sum_type]
    simp only [unary,inputs,channelTag,literal,Sum.elim_inl,Sum.elim_inr,id_eq,
      Finset.prod_const_one,mul_one,no_swap_word,endpoint,u,mapped,site]
  have ev : (∏ e ∈ E, binary none none X inputs e) =
      ∏ i : V, ∏ j : V, if i < j ∧ H.Adj i j then w (.inr (i,j,X' i,X' j)) else 1 := by
    rw [← Fintype.prod_prod_type (fun p : V × V => if p.1<p.2 ∧ H.Adj p.1 p.2 then
      w (.inr (p.1,p.2,X' p.1,X' p.2)) else 1)]
    rw [← Finset.prod_filter]
    change (∏ e ∈ (pairs H).image (chosen π), binary none none X inputs e) =
      ∏ p ∈ pairs H, w (.inr (p.1,p.2,X' p.1,X' p.2))
    rw [Finset.prod_image (chosen_inj π H)]
    apply Finset.prod_congr rfl
    intro p hp
    let e := chosen π p
    have he : e ∈ E := Finset.mem_image_of_mem _ hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    change literal w (channelTag π E (e.1,.inr (e.2.1,e.2.2,_,_))) = _
    simp only [channelTag,if_pos he,literal,Sum.elim_inl,no_swap_word]
    change w (edgeKey (π (ends e).1) (π (ends e).2) (indexWord L (X (ends e).1)) (indexWord L (X (ends e).2))) = _
    rcases chosen_ends π p with he|he
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,hlt,if_true,mapped']
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,not_lt_of_gt hlt,if_false,mapped']
  have checksOne : checks (F:=F) none none X = 1 := by simp [checks,flag,pin]
  change checks (F:=F) none none X * ((∏ v, unary none none X inputs v) *
      ∏ e ∈ E, binary none none X inputs e) = _
  rw [checksOne,one_mul,uv,ev]

end VWZClique.WeightedProof
end

/- CliqueDyadic -/
section
/-! Exact clearing of power-of-two denominators in integer matrix products. -/

namespace VWZClique.Dyadic
open scoped BigOperators

def value (q : ℕ) (z : ℤ) : ℚ := (z:ℚ)/(2:ℚ)^q

/-- Raising all entries to a common denominator preserves the exact rational. -/
theorem widen {q Q : ℕ} (h : q ≤ Q) (z : ℤ) :
    value Q (z * (2:ℤ)^(Q-q)) = value q z := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  simp [value, pow_add]
  field_simp

end VWZClique.Dyadic
end

/- UniformFoldWeights -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- Reindexing every value table by the same domain permutation leaves the pattern sum unchanged. -/
def permuteKey {n : ℕ} (e : Equiv.Perm (Fin n)) : WeightKey n → WeightKey n
  | .inl (i,x) => .inl (i,e x)
  | .inr (i,j,x,y) => .inr (i,j,e x,e y)

theorem permute_domain {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V)
    (w : WeightKey n → F) (e : Equiv.Perm (Fin n)) :
    weightedSum H (fun k => w (permuteKey e k)) = weightedSum H w := by
  classical
  unfold weightedSum
  let p := (Equiv.refl V).arrowCongr e
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  change (∑ a, f (p a)) = ∑ a, f a
  exact p.sum_comp f

theorem inputKey_eq {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (k : ChannelKey L) :
    literal w (inputKey π E k) =
      literal (fun j => w (permuteKey ((indexWord L).symm.trans (wordIndex L)) j)) (channelTag π E k) := by
  rcases k with ⟨h,⟨s,x⟩|⟨s,t,x,y⟩⟩
  · cases s <;> simp [inputKey,channelTag,literal,permuteKey]
  · by_cases hs : (h,s,t) ∈ E
    · simp only [inputKey,channelTag,if_pos hs,literal,Sum.elim_inl]
      unfold edgeKey
      split <;> simp [permuteKey]
    · simp [inputKey,channelTag,literal,hs]

theorem input_exact {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (inputKey π (slots π H) j)) =
      weightedSum H w := by
  simp_rw [inputKey_eq]
  rw [encode_graph,permute_domain]

private theorem collect_identity {F I T : Type*} [Field F] [Fintype T] {n : ℕ}
    (H : SimpleGraph V) (ep : T → V × V)
    (edge : ∀ t, (ep t).1 ≠ (ep t).2 → H.Adj (ep t).1 (ep t).2)
    (f : T → Fin n → Fin n → (I → F) → F) (w : I → F) :
    weightedSum H (fun k => collect ep f k w) =
      ∑ x : V → Fin n, ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
  classical
  have take (x : V → Fin n) (b : Kind) : collect ep f (weightAt x b) w =
      ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = b), f t (x (ep t).1) (x (ep t).2) w := by
    have hs : shape (weightAt x b) = b := by cases b with | inl _ => rfl | inr v => rcases v with ⟨_,_⟩; rfl
    unfold collect
    rw [hs]
    refine Finset.prod_congr rfl ?_
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    subst b
    rw [(value_at_ends x (ep t)).1,(value_at_ends x (ep t)).2]
  have inactive (x : V → Fin n) (i j : V) (h : ¬ (i < j ∧ H.Adj i j)) :
      collect ep f (weightAt x (.inr (i,j))) w = 1 := by
    rw [take]
    apply Finset.prod_eq_one
    intro t ht
    obtain ⟨hlt,hp|hp⟩ := oriented _ _ _ (Finset.mem_filter.mp ht).2
    · have hadj := edge t (by simpa [hp] using hlt.ne)
      exact (h ⟨hlt, by simpa [hp] using hadj⟩).elim
    · have hadj := edge t (by simpa [hp] using hlt.ne')
      exact (h ⟨hlt, by simpa [hp] using hadj.symm⟩).elim
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro x _
  have allKeys : (∏ b : Kind, collect ep f (weightAt x b) w) =
      ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
    simp_rw [take]
    exact Finset.prod_fiberwise _ _ _
  rw [← allKeys,Fintype.prod_sum_type,Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j ∧ H.Adj i j
  · simp [h,weightAt]
  · simpa only [if_neg h] using (inactive x i j h).symm

theorem updated_exact {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    weightedSum (foldedGraph a b E) (updated E a b w) = placedFold E a b w := by
  let ep := ends (E:=E) a b
  have he (t : FoldToken E) (hn : (ep t).1 ≠ (ep t).2) :
      (foldedGraph a b E).Adj (ep t).1 (ep t).2 := by
    rcases t with i|⟨h,i⟩|e
    · exact (hn rfl).elim
    · exact (hn rfl).elim
    · exact folded_adj a b E e.val e.property hn
  unfold updated
  rw [collect_identity (foldedGraph a b E) ep he,reindexed]
  let g := Equiv.piCongrRight (fun _ : V => (wordIndex L).symm)
  let f := fun X : V → Bits L => ∏ t : FoldToken E, weight a b t (X (ep t).1) (X (ep t).2) w
  change (∑ x, f (g x)) = _
  rw [g.sum_comp f]
  exact Finset.sum_congr rfl fun X _ => token_product a b E X w

theorem token_property {F : Type*} [Field F] {L : ℕ} (P : F → Prop)
    (pz : P 0) (po : P 1) (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → F) (pw : ∀ k, P (w k))
    (t : FoldToken E) (s u : Bits L) : P (weight a b t s u w) := by
  rcases t with i|⟨h,i⟩|e
  · have hh (m : Option (Mask L)) (rd : Quad → Bool) : P (flag m rd s) := by
      unfold flag
      split <;> assumption
    fin_cases i <;> exact hh _ _
  · exact pw _
  · exact pw _

theorem binary_prod {T : Type*} (s : Finset T) (f : T → ℚ)
    (h : ∀ t ∈ s, Binary (f t)) : Binary (∏ t ∈ s,f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Binary]
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp [Binary,hi,h₁,h₂]

theorem updated_binary {L : ℕ} (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → ℚ) (h : ∀ k, Binary (w k)) (k : WeightKey (2^L)) :
    Binary (updated E a b w k) := by
  apply binary_prod
  intro t _
  exact token_property Binary (Or.inl rfl) (Or.inr rfl) E a b w h t _ _

end VWZClique.UniformFolds
end

/- DoubleIdentity -/
section
open VWZClique

namespace VWZClique.Double

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

noncomputable def leftEntry (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) (u : Node Λ) (v : Node Γ) : F :=
  (d u.1 * e v.1) * ∑ y : PairBits L, (basisEntry v.1 y : F) *
    ∑ x : PairBits L, (basisEntry u.1 x : F) * channel w 0 (block x u.2) (block y v.2)

noncomputable def midEntry (Γ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (v : Node Γ) (c : Block L) : F :=
  ∑ y' : PairBits L, (basisEntry v.1 y' : F) * channel w 1 (block y' v.2) c

noncomputable def rightEntry (Λ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (c : Block L) (u : Node Λ) : F :=
  ∑ x' : PairBits L, (basisEntry u.1 x' : F) * channel w 2 c (block x' u.2)

private theorem projection_subtype (S : Finset (BasisLabel L)) (d : BasisLabel L → F)
    (x x' : PairBits L) :
    projected S d x x' = ∑ j : S, d j * (basisEntry j x : F) * (basisEntry j x' : F) := by
  exact (Finset.sum_attach S (fun j => d j * (basisEntry j x : F) * (basisEntry j x' : F))).symm

private theorem distribute (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (x x' y y' : PairBits L) (a b c : F) :
    projected Λ d x x' * projected Γ e y y' * a * b * c =
    ∑ j : Λ, ∑ k : Γ, ((d j * e k) * ((basisEntry k y : F) * ((basisEntry j x : F) * a))) *
      (((basisEntry k y' : F) * b) * ((basisEntry j x' : F) * c)) := by
  simp only [projection_subtype, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem reorder {Z C X J K R : Type*} [Fintype Z] [Fintype C] [Fintype X]
    [Fintype J] [Fintype K] [AddCommMonoid R]
    (f : Z → Z → C → X → X → X → X → J → K → R) :
    (∑ z, ∑ a, ∑ c, ∑ x, ∑ x', ∑ y, ∑ y', ∑ j, ∑ k, f z a c x x' y y' j k) =
    ∑ j, ∑ z, ∑ k, ∑ a, ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', f z a c x x' y y' j k := by
  let E : (J × Z × K × Z × C × X × X × X × X) ≃
      (Z × Z × C × X × X × X × X × J × K) :=
    { toFun := fun ⟨j,z,k,a,c,y,x,y',x'⟩ => (z,a,c,x,x',y,y',j,k)
      invFun := fun ⟨z,a,c,x,x',y,y',j,k⟩ => (j,z,k,a,c,y,x,y',x')
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : Z × Z × C × X × X × X × X × J × K → R :=
    fun ⟨z,a,c,x,x',y,y',j,k⟩ => f z a c x x' y y' j k
  simpa only [Fintype.sum_prod_type, E, Equiv.coe_fn_mk, g] using (E.sum_comp g).symm

omit [CharZero F] in
private theorem contract_sums {C X : Type*} [Fintype C] [Fintype X]
    (q : F) (s : X → F) (a : X → X → F) (b : C → X → F) (h : C → X → F) :
    q * (∑ y, s y * ∑ x, a y x) * (∑ c, (∑ y', b c y') * ∑ x', h c x') =
    ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', (q * (s y * a y x)) * (b c y' * h c x') := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum _ _ (s y), Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, Finset.mul_sum _ (b c), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x' _
  ring

/-- Expanding both projection kernels gives a three-matrix trace. -/
theorem trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F) (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w =
      ∑ u : Node Λ, ∑ v : Node Γ,
        leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u := by
  classical
  unfold doubleProjection
  simp_rw [distribute]
  rw [reorder]
  let f := fun (u : Node Λ) (v : Node Γ) =>
    leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u
  change _ = ∑ u : Node Λ, ∑ v : Node Γ, f u v
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  exact (contract_sums (d j * e k) (fun y => (basisEntry k y : F))
    (fun y x => (basisEntry j x : F) * channel w 0 (block x z) (block y a))
    (fun c y' => (basisEntry k y' : F) * channel w 1 (block y' a) c)
    (fun c x' => (basisEntry j x' : F) * channel w 2 c (block x' z))).symm

theorem matrix_trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w = Matrix.trace
      (Matrix.of (leftEntry Λ Γ d e w) *
        (Matrix.of (midEntry Γ w) * Matrix.of (rightEntry Λ w))) := by
  exact trace_identity Λ Γ d e w

end VWZClique.Double
end

/- TraceDyadicData -/
section
namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double

/-- The assignment side and common denominator of each diagonal residual. -/
def D (L : ℕ) : ℤ := 2^L

private theorem digit_cast (j : Fin 4) (s u : Bool) : (digit j s u : ℚ) = oneBit j s u := by
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_cast {L : ℕ} (j : BasisLabel L) (x : PairBits L) :
    (basisInt j x : ℚ) = basisEntry j x := by simp only [basisInt,Int.cast_prod,digit_cast,basisEntry]

private theorem bit_cast {x : ℚ} (hx : Binary x) : (bitInt x : ℚ) = x := by
  rcases hx with rfl | rfl <;> norm_num [bitInt]

theorem channel_cast {L : ℕ} (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (h : Fin 3) (a b : Block L) : (channelInt w h a b : ℚ) = channel w h a b := by
  simp only [channelInt,channel,Int.cast_mul,Int.cast_prod,fun k => bit_cast (hw k)]

theorem residual_cast (K L : ℕ) (j : BasisLabel L) :
    (residualInt K L j : ℚ) = (D L : ℚ) * (windowExpansion K L).diagonal j := by
  have h := Dyadic.widen (denominator_bits j) (residualNum (windowCoeff K L) (antisymmetric j).card)
  change (residualInt K L j : ℚ) / (2:ℚ)^L = (windowExpansion K L).diagonal j at h
  simpa [D,mul_comm] using (div_eq_iff (by positivity : (2:ℚ)^L ≠ 0)).mp h

end VWZClique.TraceDyadic
end

/- NativeSignedDivision -/
section
/-! Exact signed division on the published add/subtract/multiply word machine.
The divisor is positive. A fixed scan takes one quotient bit per iteration. -/
namespace VWZClique.IntegerRAM.SignedDivision
open Structured

/-- The inputs lie outside the range of scratch cells, so they are preserved. -/
def Frame (m out : Memory) := ∀ z : ℤ, z < signReg ∨ result < z ∧ z ≠ remn → out z = m z

private theorem frame_refl (m : Memory) : Frame m m := fun _ _ => rfl
private theorem frame_trans {m u v : Memory} (a : Frame m u) (b : Frame u v) : Frame m v :=
  fun z hz => (b z hz).trans (a z hz)

private theorem frame_tick (m : Memory) (q h : ℕ) : Frame m (nextMemory m index flag q h) := by
  intro z hz
  have h1 : z ≠ index := by rcases hz with h|h <;> norm_num [signReg,result,index] at * <;> omega
  have h2 : z ≠ flag := by rcases hz with h|h <;> norm_num [signReg,result,flag] at * <;> omega
  simp [nextMemory,update,h1,h2]

/-- After doubling the running quotient and remainder, subtract a single divisor
threshold if the doubled remainder reaches it. -/
theorem digit_runs {W : ℕ} (m : Memory) (u : m unit=1)
    (hf : Fits W (2*m remn-m threshold)) :
    ∃ f out, f≤6 ∧ Runs W digit m f out ∧
      out remn = 2*m remn - (if m threshold ≤ 2*m remn then m threshold else 0) ∧
      out result = 2*m result + (if m threshold ≤ 2*m remn then 1 else 0) ∧
      (∀ z, z ≠ remn → z ≠ result → z ≠ flag → out z=m z) := by
  let a := update m result (m result+m result)
  let b := update a remn (a remn+a remn)
  let c := update b flag (b remn-b threshold)
  have ca : c flag = 2*m remn-m threshold := by simp [c,b,a,update,flag,threshold,remn,result,two_mul]
  have left : Runs W (.atom (.add result result result)) m 1 a := .atom (.add ..)
  have middle : Runs W (.atom (.add remn remn remn)) a 1 b := .atom (.add ..)
  have test : Runs W (.atom (.sub flag remn threshold)) b 1 c := .atom (.sub ..)
  by_cases good : m threshold ≤ 2*m remn
  · let d := update c remn (c remn-c threshold)
    let e := update d result (d result+d unit)
    have act : Runs W save c 2 e := .seq (.atom (.sub ..)) (.atom (.add ..))
    refine ⟨6,e,le_rfl,.seq left (.seq middle (.seq test (.guard_take (by rwa [ca]) (by rw [ca]; omega) act))),?_,?_,?_⟩
    · rw [if_pos good]; simp [e,d,c,b,a,update,flag,threshold,remn,result,two_mul]
    · rw [if_pos good]; simp [e,d,c,b,a,update,flag,threshold,remn,result,unit,two_mul] at u ⊢
      omega
    · intro z hr hq hflag; simp [e,d,c,b,a,update,hr,hq,hflag]
  · refine ⟨4,c,by decide,.seq left (.seq middle (.seq test (.guard_skip (by rwa [ca]) (by rw [ca]; omega)))),?_,?_,?_⟩
    · rw [if_neg good]; simp [c,b,a,update,flag,threshold,remn,result,two_mul]
    · rw [if_neg good]; simp [c,b,a,update,flag,threshold,remn,result,two_mul]
    · intro z hr hq hflag; simp [c,b,a,update,hr,hq,hflag]

/-- The input remainder A is in [0,D). After h iterations, Q D + R = 2^h A,
with R in [0,D). The bound counts all arithmetic, tests and loop instructions. -/
theorem scan_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M)
    (room : Graph.Division.Room W M) {D A : ℤ} (hD : D≤(M:ℤ)) (a0 : 0≤A) (aD : A<D)
    (m : Memory) (mi : m index=0) (mu : m unit=1) (mh : m length=h)
    (mq : m result=0) (mr : m remn=A) (md : m threshold=D) :
    ∃ f out, f≤h*9 ∧ Runs W scan m f out ∧ Frame m out ∧
      0≤out remn ∧ out remn<D ∧ out result*D+out remn=(2:ℤ)^h*A ∧ out signReg=m signReg := by
  let inv := fun (j : ℕ) (x : Memory) =>
    x index=j ∧ x unit=1 ∧ x length=h ∧ x threshold=D ∧
    0≤x remn ∧ x remn<D ∧ x result*D+x remn=(2:ℤ)^j*A ∧ Frame m x ∧ x signReg=m signReg
  have init : inv 0 m := ⟨by simpa using mi,mu,mh,md,by omega,by omega,by simp [mq,mr],frame_refl m,rfl⟩
  have guard (q : ℕ) (hq : q≤h) : Fits W ((q:ℤ)-h) := by apply room.fits <;> omega
  have step (q : ℕ) (_ : q<h) (x : Memory) (hx : inv q x) :
      ∃ f : ℕ, f≤6 ∧ ∃ y : Memory, Runs W digit x f y ∧ y index=q ∧ y unit=1 ∧ y length=h ∧
        inv (q+1) (nextMemory y index flag q h) := by
    obtain ⟨xi,xu,xh,xd,rl,rh,eqn,fr,sg⟩ := hx
    obtain ⟨f,y,hf,run,yr,yq,kept⟩ := digit_runs x xu
      (by rw [xd]; apply room.fits <;> omega)
    have yi := (kept index (by decide) (by decide) (by decide)).trans xi
    have yu := (kept unit (by decide) (by decide) (by decide)).trans xu
    have yh := (kept length (by decide) (by decide) (by decide)).trans xh
    have yd := (kept threshold (by decide) (by decide) (by decide)).trans xd
    have fr' : Frame x y := by
      intro z hz; apply kept z <;> rcases hz with hh|hh <;> norm_num [remn,result,signReg,flag] at * <;> omega
    refine ⟨f,hf,y,run,yi,yu,yh,?_⟩
    have rng : 0≤y remn ∧ y remn<D := by rw [yr,xd]; split <;> omega
    have coeff : y result*D+y remn=2^(q+1)*A := by
      rw [yr,yq,xd,pow_succ]
      split <;> nlinarith only [eqn]
    have ys := (kept signReg (by decide) (by decide) (by decide)).trans sg
    refine ⟨?_,?_,?_,?_,?_,?_,?_,frame_trans fr (frame_trans fr' (frame_tick y q h)),?_⟩ <;>
      simp_all [nextMemory,update,index,flag,unit,length,threshold,remn,result,signReg]
  obtain ⟨f,hf,y,run,hy⟩ := repeatN_runs (W:=W) (B:=6) hh digit (by decide : length ≠ index)
    inv guard step init
  exact ⟨f,y,hf,run,hy.2.2.2.2.2.2.2.1,hy.2.2.2.2.1,hy.2.2.2.2.2.1,hy.2.2.2.2.2.2.1,hy.2.2.2.2.2.2.2.2⟩

theorem scale_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    (m : Memory) (mi : m index=0) (mu : m unit=1) (mh : m length=h) :
    ∃ f out, f≤h*4 ∧ Runs W scale m f out ∧ out threshold=2^h*m threshold ∧
      ∀ z, z ≠ threshold → z ≠ index → z ≠ flag → out z=m z := by
  let inv := fun (j : ℕ) (x : Memory) => x index=j ∧ x unit=1 ∧ x length=h ∧
    x threshold=2^j*m threshold ∧ ∀ z, z ≠ threshold → z ≠ index → z ≠ flag → x z=m z
  have init : inv 0 m := ⟨by simpa using mi,mu,mh,by simp,fun _ _ _ _ => rfl⟩
  have guard (q : ℕ) (hq : q≤h) : Fits W ((q:ℤ)-h) := by apply room.fits <;> omega
  have step (q : ℕ) (_ : q<h) (x : Memory) (hx : inv q x) :
      ∃ f : ℕ, f≤1 ∧ ∃ y : Memory, Runs W grow x f y ∧ y index=q ∧ y unit=1 ∧ y length=h ∧
        inv (q+1) (nextMemory y index flag q h) := by
    obtain ⟨xi,xu,xh,xd,fr⟩ := hx
    let y := update x threshold (x threshold+x threshold)
    have act : Runs W grow x 1 y := .atom (.add ..)
    refine ⟨1,le_rfl,y,act,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [y,update,index,threshold] using xi
    · simpa [y,update,unit,threshold] using xu
    · simpa [y,update,length,threshold] using xh
    · simp [nextMemory,update,index,flag]
    · simpa [nextMemory,y,update,index,flag,unit,threshold] using xu
    · simpa [nextMemory,y,update,index,flag,length,threshold] using xh
    · simp [nextMemory,y,update,index,flag,threshold,xd,pow_succ]; ring
    · intro z hd hi hf; simpa [nextMemory,y,update,hd,hi,hf] using fr z hd hi hf
  obtain ⟨f,hf,y,run,hy⟩ := repeatN_runs (W:=W) (B:=1) hh grow (by decide : length ≠ index) inv guard step init
  exact ⟨f,y,hf,run,hy.2.2.2.1,hy.2.2.2.2⟩

theorem init_runs {W : ℕ} (m : Memory) (hf : Fits W (m value)) :
    ∃ f out, f≤9 ∧ Runs W initCode m f out ∧ Frame m out ∧
      out index=0 ∧ out unit=1 ∧ out result=0 ∧ out threshold=m divisor ∧
      out remn=|(m value)| ∧
      out signReg=(if m value<0 then -1 else 1) := by
  let a := update m unit 1
  let b := update a index (a index-a index)
  let c := update b result (b result-b result)
  let d := update c threshold (c divisor*c unit)
  let e := update d remn (d result-d value)
  let g := update e signReg (e result-e unit)
  have pre : ∀ {v : ℕ} {out : Memory},
     Runs W (.whenNonnegative value (.seq (.atom (.mul remn value unit)) (.atom (.one signReg)))) g v out →
     Runs W initCode m (1+(1+(1+(1+(1+(1+v)))))) out := fun act =>
    .seq (.atom (.one ..)) (.seq (.atom (.sub ..)) (.seq (.atom (.sub ..))
      (.seq (.atom (.mul ..)) (.seq (.atom (.sub ..)) (.seq (.atom (.sub ..)) act)))))
  have gv : g value=m value := by simp [g,e,d,c,b,a,update,value,signReg,remn,result,index,unit,threshold]
  by_cases neg : m value<0
  · refine ⟨7,g,by decide,pre (.guard_skip (by rwa [gv]) (by rwa [gv])),?_,?_,?_,?_,?_,?_,?_⟩
    · intro z hz
      simp [g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit] at *
      split_ifs <;> omega
    all_goals simp [g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit,divisor,value,neg,abs_of_neg neg] at *
  · let j := update g remn (g value*g unit)
    let k := update j signReg 1
    have run : Runs W (.seq (.atom (.mul remn value unit)) (.atom (.one signReg))) g 2 k :=
      .seq (.atom (.mul ..)) (.atom (.one ..))
    refine ⟨9,k,by decide,pre (.guard_take (by rwa [gv]) (by rwa [gv]) run),?_,?_,?_,?_,?_,?_,?_⟩
    · intro z hz
      simp [k,j,g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit] at *
      split_ifs <;> omega
    all_goals simp [k,j,g,e,d,c,b,a,update,signReg,threshold,remn,result,index,unit,divisor,value,
      neg,abs_of_nonneg (le_of_not_gt neg)] at *

/-- Signed truncating quotient, in at most 13h+11 instructions. A positive
divisor d may be arbitrary, and h bounds the quotient bit length. -/
theorem divide_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    {d : ℕ} (hd : 0<d) (capacity : (2:ℤ)^h*d≤(M:ℤ)) (m : Memory)
    (bound : |m value|<(2:ℤ)^h*d) (md : m divisor=d) (mh : m length=h) :
    ∃ f out, f≤13*h+11 ∧ Runs W command m f out ∧ Frame m out ∧
      out result=(|m value|/(d:ℤ))*(if m value<0 then -1 else 1) := by
  let D := (2:ℤ)^h*d
  have dp : (0:ℤ)<d := by exact_mod_cast hd
  have aD : |m value|<D := bound
  have vf : Fits W (m value) := by
    apply room.fits <;> have v := abs_le.mp ((le_of_lt aD).trans capacity) <;> omega
  obtain ⟨f,a,hf,start,fr,ai,au,aq,ad,ar,asign⟩ := init_runs m vf
  have al := (fr length (by decide)).trans mh
  obtain ⟨g,b,hg,growRun,bd,bfix⟩ := scale_runs hh hM room a ai au al
  have bd' : b threshold=D := by rw [bd,ad,md]
  let c := update b index (b index-b index)
  have reset : Runs W (.atom (.sub index index index)) b 1 c := .atom (.sub ..)
  have cfix {j : ℤ} (hj : j≠index) (ht : j≠threshold) (hf : j≠flag) : c j=a j := by
    simpa [c,update,hj] using bfix j ht hj hf
  obtain ⟨s,v,hs,run,frame,rl,rh,eqn,vs⟩ := scan_runs hh hM room capacity (abs_nonneg _) aD c
    (by simp [c,update]) ((cfix (by decide) (by decide) (by decide)).trans au)
    ((cfix (by decide) (by decide) (by decide)).trans al)
    ((cfix (by decide) (by decide) (by decide)).trans aq)
    ((cfix (by decide) (by decide) (by decide)).trans ar)
    (by simpa [c,update,index,threshold] using bd')
  have frbc : Frame a c := by
    intro j hj; apply cfix <;> rcases hj with x|x <;> norm_num [signReg,threshold,flag,index,result] at * <;> omega
  -- The scan also preserves its caller's sign cell, which sits in the writable
  -- interval used by initialization. Recover this through the scan frame below.
  have positive : 0<(2:ℤ)^h := by positivity
  have ans : v result=|m value|/(d:ℤ) := by
    symm
    apply (Int.ediv_eq_iff_of_pos dp).2
    constructor
    · apply le_of_mul_le_mul_left (a:= (2:ℤ)^h) _ positive
      nlinarith only [eqn,rl]
    · apply lt_of_mul_lt_mul_left (a:= (2:ℤ)^h) _ positive.le
      nlinarith only [eqn,rh]
  have vsign := vs.trans ((cfix (j:=signReg) (by decide) (by decide) (by decide)).trans asign)
  let out := update v result (v result*v signReg)
  have last : Runs W (.atom (.mul result result signReg)) v 1 out := .atom (.mul ..)
  refine ⟨f+(g+(1+(s+1))),out,by omega,.seq start (.seq growRun (.seq reset (.seq run last))),?_,?_⟩
  · apply frame_trans fr (frame_trans frbc (frame_trans frame _))
    intro j hj
    have ne : j≠result := by rcases hj with hh|hh <;> norm_num [signReg,result] at * <;> omega
    simp [out,update,ne]
  · change v result*v signReg=_
    rw [ans,vsign]

/-- Every exact multiple recovers its original signed factor. -/
theorem exact_runs {W h M : ℕ} (hh : 0<h) (hM : h≤M) (room : Graph.Division.Room W M)
    {d : ℕ} (hd : 0<d) (z : ℤ) (hz : |z|<(2:ℤ)^h)
    (capacity : (2:ℤ)^h*d≤(M:ℤ)) (m : Memory) (mv : m value=z*d)
    (md : m divisor=d) (mh : m length=h) :
    ∃ f out, f≤13*h+11 ∧ Runs W command m f out ∧ Frame m out ∧ out result=z := by
  have dp : (0:ℤ)<d := by exact_mod_cast hd
  have ab : |m value|=|z| * d := by rw [mv,abs_mul,abs_of_pos dp]
  obtain ⟨f,out,cost,run,fr,answer⟩ := divide_runs hh hM room hd capacity m
    (by rw [ab]; exact mul_lt_mul_of_pos_right hz dp) md mh
  refine ⟨f,out,cost,run,fr,?_⟩
  rw [answer,ab,Int.mul_ediv_cancel _ (ne_of_gt dp),mv]
  by_cases hneg : z<0
  · rw [if_pos (mul_neg_of_neg_of_pos hneg dp),abs_of_neg hneg]; ring
  · rw [if_neg (not_lt_of_ge (mul_nonneg (by omega) dp.le)),abs_of_nonneg (by omega)]; ring

end VWZClique.IntegerRAM.SignedDivision
end

/- NativeFoldBits -/
section
namespace VWZClique.IntegerRAM.FoldBits
open Structured

def write (m : Memory) : Atom → Memory
  | .one d => update m d 1
  | .add d i j => update m d (m i + m j)
  | .sub d i j => update m d (m i - m j)
  | .mul d i j => update m d (m i * m j)
  | .load d i => update m d (m (m i))
  | .store i j => update m (m i) (m j)

def safe (W : ℕ) (m : Memory) : Atom → Prop
  | .load _ i | .store i _ => Fits W (m i)
  | _ => True

def Safe (W : ℕ) (m : Memory) : List Atom → Prop
  | [] => True
  | h :: t => safe W m h ∧ Safe W (write m h) t

theorem code_runs (W : ℕ) (xs : List Atom) (m : Memory) (hf : Safe W m xs) :
    Runs W (code xs) m xs.length (xs.foldl write m) := by
  induction xs generalizing m with
  | nil => exact .skip m
  | cons h xs ih =>
    have step : Step W h m (write m h) := by
      cases h with
      | one => exact .one ..
      | add => exact .add ..
      | sub => exact .sub ..
      | mul => exact .mul ..
      | load => exact .load _ _ _ hf.1
      | store => exact .store _ _ _ hf.1
    simpa only [code,List.foldl_cons,List.length_cons,Nat.add_comm 1] using
      Runs.seq (Runs.atom step) (ih (write m h) hf.2)

end VWZClique.IntegerRAM.FoldBits
end

/- CliqueBlockMM -/
section
/-! Fixed integer-coefficient bilinear schemes recursively multiply arbitrary
    tensor powers of their base dimension. Clearing the base coefficients'
    denominators introduces just one fixed scale factor per level. -/

namespace VWZClique.BlockMM
open scoped BigOperators

/-- Apply one coefficient vector to the blocks of a matrix. -/
def collect {I : Type*} {b : ℕ} (L : Square (Fin b)) (A : Square (Fin b × I)) : Square I :=
  fun u v => linear L (fun i j => A (i,u) (j,v))

/-- The scalar scheme is valid with integer matrices as its entries. -/
theorem scheme_blocks {I : Type*} [Fintype I] {b r : ℕ} (S : Scheme b r)
    (A B : Square (Fin b × I)) (i j : Fin b) (u v : I) :
    (∑ s, S.out i j s * (collect (S.left s) A * collect (S.right s) B) u v) =
      S.scale * (A*B) (i,u) (j,v) := by
  calc
    _ = ∑ x : I, ∑ s, S.out i j s *
          (collect (S.left s) A u x * collect (S.right s) B x v) := by
      simp only [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ x : I, S.scale * (∑ q : Fin b, A (i,u) (q,x) * B (q,x) (j,v)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact S.correct (fun p q => A (p,u) (q,x)) (fun p q => B (p,x) (q,v)) i j
    _ = _ := by
      rw [← Finset.mul_sum, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]

/-- Matrix index at recursion depth `h`. -/
def Index (b : ℕ) : ℕ → Type
  | 0 => Unit
  | h+1 => Fin b × Index b h

instance indexFintype (b : ℕ) : (h : ℕ) → Fintype (Index b h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h+1 => @instFintypeProd _ _ (inferInstanceAs (Fintype (Fin b))) (indexFintype b h)

/-- A fixed recursion on the depth, using exactly the same three coefficient tables at every node. -/
def product {b r : ℕ} (S : Scheme b r) :
    (h : ℕ) → Square (Index b h) → Square (Index b h) → Square (Index b h)
  | 0, A, B => fun i j => A i () * B () j
  | h+1, A, B => fun i j => ∑ s, S.out i.1 j.1 s *
      product S h (collect (S.left s) A) (collect (S.right s) B) i.2 j.2

theorem product_exact {b r : ℕ} (S : Scheme b r) (h : ℕ)
    (A B : Square (Index b h)) (u v : Index b h) :
    product S h A B u v = S.scale^h * (A*B) u v := by
  induction h with
  | zero =>
    change A u () * B () v = S.scale^0 * (∑ j : Unit, A u j * B j v)
    simp
  | succ h ih =>
    obtain ⟨i,u⟩ := u
    obtain ⟨j,v⟩ := v
    change (∑ s, S.out i j s * product S h (collect (S.left s) A) (collect (S.right s) B) u v) = _
    calc
      _ = S.scale^h *
          (∑ s, S.out i j s * (collect (S.left s) A * collect (S.right s) B) u v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [ih]
        ring
      _ = S.scale^h * (S.scale * (A*B) (i,u) (j,v)) :=
        congrArg (fun z : ℤ => S.scale^h*z) (scheme_blocks (I := Index b h) S A B i j u v)
      _ = _ := by rw [pow_succ]; ring

/-- Scalar budget for the tabulated schedule. A node forms the two sets of
    `r` block combinations and the `b²` output combinations, with at most
    `6rb²` coefficient products/additions per entry of a block. -/
def scalarBudget (b r : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => r*scalarBudget b r h + 6*r*b^2*(b^2)^h

theorem scalarBudget_le {b r : ℕ} (hr : b^2 ≤ r) (h : ℕ) :
    scalarBudget b r h ≤ (1+6*b^2*h)*r^h := by
  induction h with
  | zero => simp [scalarBudget]
  | succ h ih =>
    calc
      _ ≤ r*((1+6*b^2*h)*r^h) + 6*r*b^2*r^h := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ ih)
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr h))
      _ = _ := by ring

/-- For a fixed base and coefficient bound, exponential growth in the recursion
    depth is polynomial in the matrix dimension. -/
theorem depth_power_polynomial {b : ℕ} (hb : 2 ≤ b) (γ h : ℕ) :
    γ^h ≤ (b^h)^γ := by
  have hγ : γ ≤ b^γ := (Nat.lt_two_pow_self (n := γ)).le.trans (Nat.pow_le_pow_left hb _)
  calc
    γ^h ≤ (b^γ)^h := Nat.pow_le_pow_left hγ h
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end VWZClique.BlockMM
end

/- DoubleEstimates -/
section
open VWZClique Real

namespace VWZClique.Double

theorem length_bound (σ : ℝ) (hσ : 0 < σ) :
    ∃ H : ℝ, 0 < H ∧ ∀ L : ℕ, (L:ℝ)+1 ≤ H * (((2:ℝ)^L)^σ) := by
  let a : ℝ := (2 : ℝ)^σ
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hσ
  have hd : 0 < a-1 := by linarith
  refine ⟨1+1/(a-1),by positivity,?_⟩
  intro L
  have hL := one_add_mul_sub_le_pow (by linarith : -1 ≤ a) L
  have haL : 1 ≤ a^L := one_le_pow₀ ha.le
  have hs : ((2 : ℝ)^L)^σ = a^L := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  rw [hs, add_mul, one_mul,one_div_mul_eq_div]
  have hfrac : (L : ℝ) ≤ a^L/(a-1) := (le_div_iff₀ hd).mpr (by linarith)
  linarith

end VWZClique.Double
end

/- MMUniform -/
section
namespace VWZClique.BlockMM

theorem depth_bounds {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    n ≤ b^(depth b n) ∧ b^(depth b n) ≤ b*n := by
  refine ⟨(Nat.lt_pow_succ_log_self hb n).le,?_⟩
  rw [depth,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))

/-- Positional numbering of the recursively blocked index. -/
def radix (b : ℕ) : (h : ℕ) → Index b h ≃ Fin (b^h)
  | 0 => finOneEquiv.symm
  | h+1 => ((Equiv.prodCongr (Equiv.refl (Fin b)) (radix b h)).trans finProdFinEquiv).trans
      (finCongr (by rw [pow_succ,Nat.mul_comm]))

def includeIndex {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) : Fin n ↪ Index b (depth b n) :=
  (Fin.castLEEmb (depth_bounds hb hn).1).trans (radix b _).symm.toEmbedding

noncomputable def padded {I J : Type*} (e : I ↪ J) (A : Square I) : Square J :=
  fun i j => (Function.partialInv e i).elim 0 fun u => (Function.partialInv e j).elim 0 (A u)

theorem padded_product {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (A B : Square I) (i j : I) :
    (padded e A * padded e B) (e i) (e j) = (A*B) i j := by
  classical
  simp only [Matrix.mul_apply,padded,Function.partialInv_left e.injective,Option.elim_some]
  let s := Finset.univ.map e
  have hu : s ⊆ Finset.univ := Finset.subset_univ s
  rw [← Finset.sum_subset hu (f := fun k =>
      (Function.partialInv e k).elim 0 (A i) * (Function.partialInv e k).elim 0 (fun u => B u j))
      (by
        intro k _ hk
        cases h : Function.partialInv e k with
        | none => simp
        | some a =>
          exact (hk (by simp [s,← (e.injective.isPartialInv a k).1 h])).elim)]
  simp [s,Function.partialInv_left e.injective]

/-- Result of applying the one fixed scheme at every node of the uniformly padded recursion. -/
noncomputable def scaled {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) : Square (Fin n) :=
  let e := includeIndex hb hn
  fun i j => product S (depth b n) (padded e A) (padded e B) (e i) (e j)

theorem scaled_exact {b r n : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (A B : Square (Fin n)) (i j : Fin n) :
    scaled S hb hn A B i j = S.scale^(depth b n) * (A*B) i j := by
  simp only [scaled,product_exact,padded_product]

theorem scaled_div {b r n : ℕ} (S : Scheme b r) (hs : S.scale ≠ 0)
    (hb : 2 ≤ b) (hn : 1 ≤ n) (A B : Square (Fin n)) (i j : Fin n) :
    scaled S hb hn A B i j / S.scale^(depth b n) = (A*B) i j := by
  rw [scaled_exact,Int.mul_ediv_cancel_left _ (pow_ne_zero _ hs)]

theorem depth_poly {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (γ : ℕ) :
    γ^(depth b n) ≤ (b*n)^γ :=
  (depth_power_polynomial hb _ _).trans (Nat.pow_le_pow_left (depth_bounds hb hn).2 _)

private theorem pow_swap (x : ℝ) (hx : 0 ≤ x) (α : ℝ) (h : ℕ) :
    (x^α)^h = (x^h)^α := by
  rw [← Real.rpow_natCast_mul hx, mul_comm, Real.rpow_mul_natCast hx]

/-- For every exponent bounding the fixed rank, the shared block schedule at
arbitrary side n satisfies the positive-slack cost bound. -/
theorem uniform_budget {b r : ℕ} (hb : 2 ≤ b) (hr : b^2 ≤ r)
    (τ : ℝ) (hτ : 0 ≤ τ) (hrate : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (scalarBudget b r (depth b n) : ℝ) ≤ C*(n:ℝ)^(τ+ε) := by
  obtain ⟨H,hH,hH'⟩ := Double.length_bound ε hε
  let D : ℝ := 1+6*(b:ℝ)^2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*H*(b:ℝ)^(τ+ε),by positivity,?_⟩
  intro n hn
  let h := depth b n
  have hp : (b^h:ℕ) ≤ b*n := (depth_bounds hb hn).2
  have hp' : (b:ℝ)^h ≤ (b:ℝ)*n := by exact_mod_cast hp
  have htwo : (2:ℝ)^h ≤ (b:ℝ)^h := by gcongr; exact_mod_cast hb
  have hlin : 1+6*(b:ℝ)^2*h ≤ D*(H*((b:ℝ)^h)^ε) := by
    calc
      _ ≤ D*((h:ℝ)+1) := by dsimp [D]; nlinarith [sq_nonneg (b:ℝ), Nat.cast_nonneg (α := ℝ) h]
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hH' h).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) htwo hε.le) hH.le)) hD.le
  have hpow : (r:ℝ)^h ≤ ((b:ℝ)^h)^τ := by
    rw [← pow_swap _ (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hrate h
  have hs := scalarBudget_le hr h
  have hs' : (scalarBudget b r h : ℝ) ≤ (1+6*(b:ℝ)^2*h)*(r:ℝ)^h := by exact_mod_cast hs
  calc
    _ ≤ _ := hs'.trans (mul_le_mul hlin hpow (by positivity) (by positivity))
    _ = D*H*(((b:ℝ)^h)^(τ+ε)) := by
      rw [Real.rpow_add (by positivity)]; ring
    _ ≤ D*H*(((b:ℝ)*n)^(τ+ε)) := by
      gcongr
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

end VWZClique.BlockMM
end

/- NativeProjectionScaleBound -/
section
namespace VWZClique.IntegerRAM.Projected
open BlockMM

def commonScale (c b L s : ℕ) := (c^(depth b (2^L)))^3*c^(depth b s)
def scaleBits (c L : ℕ) := c*(6*L+4)

/-- Both matrix depths are logarithmic in the assignment-domain size; the
largest square has side at most (2^L)^3. All scheme constants are fixed. -/
theorem scale_bound {c b L s : ℕ} (hc : 0<c) (hb : 2≤b) (hs : s≤(2^L)^3) :
    0<commonScale c b L s ∧ commonScale c b L s≤2^(scaleBits c L) := by
  have lg (p : ℕ) : Nat.log b (2^p) ≤ p := by
    simpa only [Nat.log_pow (by decide : 1<(2:ℕ))] using Nat.log_anti_left (n:=2^p) (by decide : 1<(2:ℕ)) hb
  have low := lg L
  have hs' : s≤2^(L*3) := by simpa only [pow_mul] using hs
  have hi := (Nat.log_mono_right (b:=b) hs').trans (lg (L*3))
  have H : depth b (2^L)*3+depth b s≤6*L+4 := by unfold depth; omega
  refine ⟨by unfold commonScale; positivity,?_⟩
  calc
    _ = c^(depth b (2^L)*3+depth b s) := by rw [pow_add,pow_mul]; rfl
    _ ≤ c^(6*L+4) := Nat.pow_le_pow_right hc H
    _ ≤ (2^c)^(6*L+4) := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = _ := (pow_mul _ _ _).symm

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionNormalize -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured SignedDivision

def normalizeRoom (c L : ℕ) := 2^(23*L+3+scaleBits c L)

theorem normalizeRoom_polynomial (c L : ℕ) :
    normalizeRoom c L=2^(3+4*c)*(2^L)^(23+6*c) := by
  unfold normalizeRoom scaleBits
  rw [←pow_mul,←pow_add]
  congr 1
  ring

theorem normalize_capacity {c b L s : ℕ} (hc : 0<c) (hb : 2≤b) (hs : s≤(2^L)^3) :
    2^(21*L+3)*((2^L)^2*commonScale c b L s)≤normalizeRoom c L := by
  obtain ⟨_,hQ⟩ := scale_bound hc hb hs
  calc
    _ ≤ 2^(21*L+3)*((2^L)^2*2^(scaleBits c L)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQ)
    _ = _ := by unfold normalizeRoom;rw [←pow_mul,←Nat.mul_assoc,←pow_add,←pow_add];congr 1;ring

abbrev rawTrace : ℤ := -44
abbrev scaleReg : ℤ := -45

/-- Assemble P_small³ P_large from the scales returned by the two square sizes.
The accumulator at −44 and both scale sources are preserved. -/
def combineScales (small large : ℤ) : Command := .seq (.atom (.mul scaleReg small small))
  (.seq (.atom (.mul scaleReg scaleReg small)) (.atom (.mul scaleReg scaleReg large)))

theorem combineScales_runs {W : ℕ} (small large : ℤ) (hs : small≠scaleReg) (hl : large≠scaleReg)
    (m : Memory) :
    ∃ o, Runs W (combineScales small large) m 3 o ∧ o scaleReg=(m small)^3*m large ∧
      ∀ j : ℤ, j≠scaleReg → o j=m j := by
  let a := update m scaleReg (m small*m small)
  let b := update a scaleReg (a scaleReg*a small)
  let o := update b scaleReg (b scaleReg*b large)
  refine ⟨o,.seq (.atom (.mul ..)) (.seq (.atom (.mul ..)) (.atom (.mul ..))),?_,?_⟩
  · simp only [o,b,a,update,eq_self,if_true,if_neg hs,if_neg hl];ring
  · intro j hj;simp [o,b,a,update,hj]

/-- Fixed preprocessing before the single exact integer division. -/
def denominator : List Atom := [.one unit,.mul value rawTrace unit,
  .mul divisor 0 0,.mul divisor divisor scaleReg,
  .add length 320 320,.add length length length,.add length length 320,
  .add length length length,.add length length length,.add length length 320,
  .add length length unit,.add length length unit,.add length length unit]

def normalize := Command.seq (FoldBits.code denominator) command

theorem normalize_runs {W c b s L : ℕ} (hc : 0<c) (hb : 2≤b) (hs : s≤(2^L)^3)
    (cap : Graph.Division.Room W (normalizeRoom c L)) (m : Memory) (z : ℤ)
    (bounded : |z|≤(2:ℤ)^(21*L+2))
    (mv : m rawTrace=(commonScale c b L s:ℤ)*((2:ℤ)^L)^2*z)
    (sc : m scaleReg=(commonScale c b L s:ℤ)) (nreg : m 0=((2^L:ℕ):ℤ)) (lreg : m 320=L) :
    ∃ T o, T≤13*(21*L+3)+24 ∧ Runs W normalize m T o ∧ o result=z ∧ ∀ j : ℕ, o j=m j := by
  let a := denominator.foldl FoldBits.write m
  have run : Runs W (FoldBits.code denominator) m 13 a := FoldBits.code_runs _ _ _ (by simp [denominator,FoldBits.safe,FoldBits.Safe])
  have av : a value=m rawTrace := by simp [a,denominator,FoldBits.write,update,value,unit,length,divisor,rawTrace]
  have qr : m (-45)=(commonScale c b L s:ℤ) := sc
  have div : a divisor=(((2^L)^2*commonScale c b L s:ℕ):ℤ) := by
    simp [a,denominator,FoldBits.write,update,value,unit,length,divisor,rawTrace,scaleReg,qr,nreg] <;> ring <;> simp
  have len : a length=((21*L+3:ℕ):ℤ) := by
    simp [a,denominator,FoldBits.write,update,value,unit,length,divisor,lreg];ring
  have before (j : ℕ) : a j=m j := by simp [a,denominator,FoldBits.write,update,value,unit,length,divisor]
  have denPos : 0<(2^L)^2*commonScale c b L s := Nat.mul_pos (by positivity) (scale_bound hc hb hs).1
  have less : |z|<(2:ℤ)^(21*L+3) := bounded.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have size : 21*L+3≤normalizeRoom c L := (Nat.lt_two_pow_self (n:=21*L+3)).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega : 21*L+3≤23*L+3+scaleBits c L))
  have valueEq : a value=z*(((2^L)^2*commonScale c b L s:ℕ):ℤ) := by rw [av,mv];push_cast;ring
  obtain ⟨f,o,hf,exe,fr,ans⟩ := exact_runs (by omega : 0<21*L+3) size cap denPos z less
    (by exact_mod_cast normalize_capacity hc hb hs) a valueEq div len
  refine ⟨_,o,by omega,.seq run exe,ans,?_⟩
  intro j;exact (fr j (Or.inr ⟨by dsimp [result];omega,by dsimp [remn];omega⟩)).trans (before j)

end VWZClique.IntegerRAM.Projected
end

/- NativeFrame -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured

theorem different (d : ℕ) {a b : Field} (h : a ≠ b) : reg d a ≠ reg d b := by
  cases a <;> cases b <;> simp_all [reg,Field.offset] <;> omega

end VWZClique.IntegerRAM.NativeFrame
end

/- NativeProjectionHeader -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured FoldBits NativeFrame

abbrev countPtr : ℤ := -50
abbrev squareTmp : ℤ := -51
abbrev cubeTmp : ℤ := -52
abbrev unitTmp : ℤ := -53
def countAddr (w n : ℕ) := w+9*n+81*(n*n)+7*n^3

def countPointer (d : ℕ) : List Atom := [.add countPtr 0 0,.add countPtr countPtr countPtr,
  .add countPtr countPtr countPtr,.add countPtr countPtr 0,.mul squareTmp countPtr countPtr,
  .add countPtr countPtr squareTmp,.add countPtr countPtr (reg d .weights),
  .mul squareTmp 0 0,.mul squareTmp squareTmp 0,.add cubeTmp squareTmp squareTmp,
  .add cubeTmp cubeTmp cubeTmp,.add cubeTmp cubeTmp cubeTmp,.sub cubeTmp cubeTmp squareTmp,
  .add countPtr countPtr cubeTmp]

theorem countPointer_runs {W n w d : ℕ} (m : Memory) (hn : m 0=n) (hw : m (reg d .weights)=w) :
    ∃ x, Runs W (code (countPointer d)) m 14 x ∧ x countPtr=countAddr w n ∧
      ∀ j : ℤ, j≠countPtr → j≠squareTmp → j≠cubeTmp → x j=m j := by
  let a := (countPointer d).foldl write m
  have pos := reg_positive d .weights
  have h₁ : reg d .weights ≠ -50 := by omega
  have h₂ : reg d .weights ≠ -51 := by omega
  have h₃ : reg d .weights ≠ -52 := by omega
  refine ⟨a,code_runs _ _ _ (by simp [countPointer,Safe,safe]),?_,?_⟩
  · simp [a,countPointer,write,update,countPtr,squareTmp,cubeTmp,hn,hw,h₁,h₂,h₃,countAddr];ring
  · intro j hj hk hl; simp [a,countPointer,write,update,hj,hk,hl]

def installFields (d : ℕ) : List Atom := [.load (reg d .leftLength) countPtr,.one unitTmp,
  .mul (reg d .rightLength) (reg d .leftLength) unitTmp,
  .mul (reg d .bothLength) (reg d .leftLength) (reg d .leftLength),
  .sub (reg d .index) unitTmp unitTmp,.mul (reg d .value) SignedDivision.result unitTmp]
def install (d : ℕ) := Command.seq (code (countPointer d)) (code (installFields d))

def off (d : ℕ) (j : ℤ) := j≠reg d .leftLength ∧ j≠reg d .rightLength ∧ j≠reg d .bothLength ∧
  j≠reg d .index ∧ j≠reg d .value

structure Installed (d n : ℕ) (z : ℤ) (m : Memory) : Prop where
  first : m (reg d .leftLength)=n
  second : m (reg d .rightLength)=n
  both : m (reg d .bothLength)=((n*n:ℕ):ℤ)
  index : m (reg d .index)=0
  value : m (reg d .value)=z

theorem install_runs {W n w d maskCount M : ℕ} (room : Graph.Division.Room W M) (space : countAddr w n≤M)
    (m : Memory) (hn : m 0=n) (hw : m (reg d .weights)=w) (count : m (countAddr w n:ℤ)=maskCount)
    (z : ℤ) (answer : m SignedDivision.result=z) :
    ∃ o, Runs W (install d) m 20 o ∧ Installed d maskCount z o ∧ ∀ j : ℤ, 0≤j → off d j → o j=m j := by
  obtain ⟨x,run,ptr,keep⟩ := countPointer_runs (W:=W) m hn hw
  have cnt : x (x countPtr)=maskCount := by rw [ptr,keep _ (by dsimp [countPtr];omega) (by dsimp [squareTmp];omega) (by dsimp [cubeTmp];omega),count]
  have result := (keep SignedDivision.result (by decide) (by decide) (by decide)).trans answer
  let o := (installFields d).foldl write x
  have fit : Fits W (x countPtr) := ptr ▸ room.fits (by omega) (by omega)
  have writeRun : Runs W (code (installFields d)) x 6 o := code_runs _ _ _
    (by simpa [installFields,Safe,safe] using fit)
  have df (a b : Field) (ne : a ≠ b) : reg d a≠reg d b := different d ne
  have neg (i : Field) (j : ℤ) (h : j≤0) : reg d i≠j := by have := reg_positive d i;omega
  have neg' (j : ℤ) (i : Field) (h : j≤0) : j≠reg d i := (neg i j h).symm
  refine ⟨o,.seq run writeRun,?_,?_⟩
  · constructor <;> simp (disch := decide) [o,installFields,write,update,df,neg,neg',unitTmp,
      SignedDivision.result,cnt,result]
  · rintro j hj ⟨hl,hr,hb,hi,hv⟩
    have hu : j≠unitTmp := by dsimp [unitTmp];omega
    simpa [o,installFields,write,update,hl,hr,hb,hi,hv,hu] using
      keep j (by dsimp [countPtr];omega) (by dsimp [squareTmp];omega) (by dsimp [cubeTmp];omega)

end VWZClique.IntegerRAM.Projected
end

/- UniformFolds -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

theorem route_static {L : ℕ} (a b : Option (Mask L)) (h : Fin 3) (s : Slot) :
    (route a b h s).1 =
      (route (representative a.isSome) (representative b.isSome) h s).1 := by
  cases s <;> fin_cases h <;> cases a <;> cases b <;> rfl

theorem graph_static {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot) (d : Branch)
    (ha : a.isSome = first d) (hb : b.isSome = second d) :
    foldedGraph a b E = child E d := by
  unfold child
  rw [← ha,← hb]
  unfold foldedGraph
  apply congrArg SimpleGraph.fromEdgeSet
  apply congrArg (fun T : Finset (Sym2 V) => (T : Set (Sym2 V)))
  apply Finset.image_congr
  intro e _
  change s((route a b e.1 e.2.1).1,(route a b e.1 e.2.2).1) = _
  rw [route_static a b e.1 e.2.1,route_static a b e.1 e.2.2]
  rfl

end VWZClique.UniformFolds
end

/- UniformFoldPaths -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

theorem Round.exact_value {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (d : Branch)
    (ha : r.a.isSome = first d) (hb : r.b.isSome = second d) :
    weightedSum (child (slots r.π r.H) d) (r.apply w) = placedFold (slots r.π r.H) r.a r.b (r.inputs w) := by
  rw [← graph_static r.a r.b _ d ha hb]
  exact updated_exact _ _ _ _

theorem Round.inputs_property {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ)
    (P : ℚ → Prop) (po : P 1) (hw : ∀ k, P (w k)) (j : ChannelKey L) : P (r.inputs w j) := by
  rcases j with ⟨h,⟨i,x⟩|⟨s,t,x,y⟩⟩
  · cases i
    · exact hw _
    · exact po
  · by_cases he : (h,s,t) ∈ slots r.π r.H
    · simpa only [Round.inputs,inputKey,if_pos he,literal,Sum.elim_inl] using hw
        (edgeKey (r.π (endpoint h s)) (r.π (endpoint h t)) (wordIndex L x) (wordIndex L y))
    · simpa only [Round.inputs,inputKey,if_neg he,literal,Sum.elim_inr,id_eq] using po

/-- For Boolean tables, the weighted sum counts a subset of the assignments. -/
theorem binary_sum {n : ℕ} (H : SimpleGraph V) (w : WeightKey n → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℕ, z ≤ n^9 ∧ weightedSum H w = (z:ℚ) := by
  classical
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  have hf (a : V → Fin n) : Binary (f a) := by
    have h₁ := binary_prod Finset.univ (fun i => w (.inl (i,a i))) (fun i _ => hw _)
    have h₂ : Binary (∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1) := by
      apply binary_prod
      intro i _
      apply binary_prod
      intro j _
      split
      · exact hw _
      · exact Or.inr rfl
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp only [f,h₁,h₂,zero_mul,one_mul,Binary] <;> simp
  let s := Finset.univ.filter (fun a => f a=1)
  refine ⟨s.card,?_,?_⟩
  · simpa [V] using Finset.card_le_univ s
  · change (∑ a, f a) = (s.card:ℚ)
    calc
      _ = ∑ a, if f a=1 then (1:ℚ) else 0 := Finset.sum_congr rfl (fun a _ => by rcases hf a with h|h <;> simp [h])
      _ = _ := by rw [← Finset.sum_filter]; simp [s]

end VWZClique.UniformFolds
end

/- UniformFoldEvaluator -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

abbrev ProjectionEval (L : ℕ) := Expansion L → (ChannelKey L → ℚ) → ℚ

theorem input_supported {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (h : Fin 3) (a b : Block L) :
    channel (r.inputs w) h a b = placedChannel (slots r.π r.H) (r.inputs w) h a b := by
  unfold Round.inputs
  simp_rw [inputKey_eq]
  exact supported _ _ _ _ _ _

/-- Each projected contribution is the trace of the three explicit channel matrices. -/
noncomputable def traceProjection (L : ℕ) : ProjectionEval L := fun q w =>
  Matrix.trace (Matrix.of (Double.leftEntry q.labels q.labels q.diagonal q.diagonal w) *
    (Matrix.of (Double.midEntry q.labels w) * Matrix.of (Double.rightEntry q.labels w)))

theorem traceProjection_correct {L : ℕ} (q : Expansion L) (w : ChannelKey L → ℚ) :
    traceProjection L q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w :=
  (Double.matrix_trace_identity _ _ _ _ _).symm

end VWZClique.UniformFolds
end

/- UniformProjectionBudget -/
section
namespace VWZClique.UniformFolds

/-- Every actual basis set fits the selected schedule, including all small lengths. -/
theorem projectionShape_all {L : ℕ} (q : ℕ) (S : Finset (BasisLabel L)) :
    let t := effectiveTile q L S.card
    S.card*2^L ≤ Double.IntegerTiling.side L t ∧
      Double.IntegerTiling.blocks L t * Double.IntegerTiling.side L t = (2^L)^3 := by
  refine ⟨?_,Double.IntegerTiling.exact_shape L _⟩
  unfold effectiveTile
  split
  · assumption
  · have hs : S.card ≤ 4^L := by simpa [BasisLabel] using Finset.card_le_univ S
    calc
      _ ≤ 4^L*2^L := Nat.mul_le_mul_right _ hs
      _ = 2^(3*L) := by rw [show (4:ℕ) = 2^2 by decide,←pow_mul,←pow_add]; congr 1; omega
      _ = _ := by simp [Double.IntegerTiling.side]

end VWZClique.UniformFolds
end

/- MMUniformField -/
section
namespace VWZClique.BlockMM

/-- Three coefficient arrays with common rank index. -/
structure Factors (F I R : Type*) where
  left : R → I → I → F
  right : R → I → I → F
  out : I → I → R → F

namespace Factors
variable {F I R J Q : Type*} [Field F]

open Classical in
def Valid [Fintype R] (T : Factors F I R) : Prop :=
  ∀ i j a d e f : I,
    (∑ s, T.out i j s * T.left s a d * T.right s e f) =
      if i=a ∧ d=e ∧ f=j then 1 else 0

def reindex (T : Factors F I R) (u : J ≃ I) (v : Q ≃ R) : Factors F J Q where
  left s a d := T.left (v s) (u a) (u d)
  right s a d := T.right (v s) (u a) (u d)
  out i j s := T.out (u i) (u j) (v s)

theorem reindex_valid [Fintype R] [Fintype Q] (T : Factors F I R) (h : T.Valid)
    (u : J ≃ I) (v : Q ≃ R) : (T.reindex u v).Valid := by
  classical
  intro i j a d e f
  change (∑ s : Q, T.out _ _ (v s) * T.left (v s) _ _ * T.right (v s) _ _) = _
  rw [v.sum_comp (fun s => T.out (u i) (u j) s * T.left s (u a) (u d) * T.right s (u e) (u f)),h]
  simp

def power (T : Factors F I R) (h : ℕ) : Factors F (Fin h → I) (Fin h → R) where
  left s a d := ∏ k, T.left (s k) (a k) (d k)
  right s e f := ∏ k, T.right (s k) (e k) (f k)
  out i j s := ∏ k, T.out (i k) (j k) (s k)

theorem power_valid [Fintype R] (T : Factors F I R) (hT : T.Valid) (h : ℕ) : (T.power h).Valid := by
  classical
  intro i j a d e f
  simp only [power,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k s => T.out (i k) (j k) s * T.left s (a k) (d k) * T.right s (e k) (f k))]
  have step (k : Fin h) := hT (i k) (j k) (a k) (d k) (e k) (f k)
  simp_rw [step]
  by_cases hx : i=a ∧ d=e ∧ f=j
  · rcases hx with ⟨rfl,rfl,rfl⟩
    simp
  · rw [if_neg hx]
    have hh : ∃ k, ¬ (i k=a k ∧ d k=e k ∧ f k=j k) := by
      by_contra! hf
      exact hx ⟨funext (fun k => (hf k).1),funext (fun k => (hf k).2.1),funext (fun k => (hf k).2.2)⟩
    obtain ⟨k,hk⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

section Rational
variable {E D : Type*} [Field E] [Algebra ℚ E] [Fintype D]

private theorem linear_expansion (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (z x y : E) :
    (∑ a, ∑ d, p (z * B a * B d) * B.repr x a * B.repr y d) = p (z*x*y) := by
  have hx : p (z*x*y) = ∑ a, B.repr x a * p (z*B a*y) := by
    conv_lhs => rw [← B.sum_repr x]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]
  have hy (a : D) : p (z*B a*y) = ∑ d, B.repr y d * p (z*B a*B d) := by
    conv_lhs => rw [← B.sum_repr y]
    simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,smul_eq_mul]
  rw [hx]
  apply Finset.sum_congr rfl
  intro a _
  rw [hy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Passing once to rational coordinates costs a fixed factor d² in rank,
independent of the tensor power to which this operation is applied. -/
noncomputable def rational (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (T : Factors E I R) :
    Factors ℚ I (R × D × D) where
  left s a d := B.repr (T.left s.1 a d) s.2.1
  right s e f := B.repr (T.right s.1 e f) s.2.2
  out i j s := p (T.out i j s.1 * B s.2.1 * B s.2.2)

theorem rational_valid [Fintype R] (B : Module.Basis D ℚ E) (p : E →ₗ[ℚ] ℚ) (hp : p 1 = 1)
    (T : Factors E I R) (hT : T.Valid) : (rational B p T).Valid := by
  classical
  intro i j a d e f
  simp only [rational,Fintype.sum_prod_type,linear_expansion]
  rw [← map_sum p,hT i j a d e f]
  by_cases h : i=a ∧ d=e ∧ f=j <;> simp [h,hp]

theorem exists_projection : ∃ p : E →ₗ[ℚ] ℚ, p 1 = 1 := by
  let incl := Algebra.linearMap ℚ E
  obtain ⟨p,h⟩ := incl.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (RingHom.injective _))
  refine ⟨p,?_⟩
  simpa [incl] using LinearMap.congr_fun h (1:ℚ)

end Rational

theorem rational_power {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (h : ℕ) :
    ∃ Q : Factors ℚ (Fin (b^h)) (Fin (r^h * (Module.finrank ℚ E)^2)), Q.Valid := by
  classical
  let d := Module.finrank ℚ E
  let u : (Fin h → Fin b) ≃ Fin (b^h) := Fintype.equivFinOfCardEq (by simp)
  let v : ((Fin h → Fin r) × Fin d × Fin d) ≃ Fin (r^h*d^2) :=
    Fintype.equivFinOfCardEq (by simp [pow_two])
  obtain ⟨p,hp⟩ := exists_projection (E := E)
  let B := Module.finBasis ℚ E
  exact ⟨_,reindex_valid _ (rational_valid B p hp (T.power h) (power_valid T hT h)) u.symm v.symm⟩

end Factors
end VWZClique.BlockMM
end

/- MMUniformInteger -/
section
namespace VWZClique.BlockMM

/-- Clear every denominator in one finite rational table using a positive common integer. -/
theorem commonDen {X : Type*} [Fintype X] (f : X → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : X → ℤ, ∀ x, (z x : ℚ) = (D:ℚ)*f x := by
  classical
  let den (x : X) := (f x).den
  refine ⟨∏ x, den x,Finset.prod_pos (fun x _ => (f x).den_pos),fun x =>
    ((∏ y ∈ Finset.univ.erase x, den y : ℕ):ℤ)*(f x).num,?_⟩
  intro x
  have hd : (den x : ℚ)*f x = (f x).num := by
    calc
      _ = (den x:ℚ)*((f x).num/(den x:ℚ)) := congrArg ((den x : ℚ) * ·) (f x).num_div_den.symm
      _ = _ := by
        have hn : (den x : ℚ) ≠ 0 := by exact_mod_cast (f x).den_nz
        field_simp
  rw [← Finset.prod_erase_mul Finset.univ den (Finset.mem_univ x)]
  push_cast
  rw [mul_assoc,hd]

private theorem expand_products {G I J R : Type*} [CommRing G] [Fintype I] [Fintype J] [Fintype R]
    (l : R → I → G) (t : R → J → G) (o : R → G) (a : I → G) (b : J → G) :
    (∑ s, o s * ((∑ p, l s p*a p)*(∑ q, t s q*b q))) =
    ∑ p, ∑ q, (∑ s, o s*l s p*t s q)*(a p*b q) := by
  classical
  calc
    _ = ∑ s, ∑ p, ∑ q, (o s*l s p*t s q)*(a p*b q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

theorem schemeOfIdentities {b r : ℕ}
    (L R : Fin r → Square (Fin b)) (O : Fin b → Fin b → Fin r → ℤ) (D : ℤ)
    (h : ∀ i j a d e f : Fin b, (∑ s, O i j s * L s a d * R s e f) =
      D * (if i=a ∧ d=e ∧ f=j then 1 else 0)) :
    ∃ S : Scheme b r, S.scale = D := by
  classical
  refine ⟨⟨L,R,O,D,?_⟩,rfl⟩
  intro A B i j
  have he := expand_products (fun s (p : Fin b × Fin b) => L s p.1 p.2)
    (fun s (p : Fin b × Fin b) => R s p.1 p.2) (O i j)
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  simp only [Fintype.sum_prod_type] at he
  calc
    _ = _ := he
    _ = _ := by
      simp_rw [h]
      have step (a d e f : Fin b) :
          D * (if i=a ∧ d=e ∧ f=j then (1:ℤ) else 0) * (A a d * B e f) =
          if a=i then if e=d then if f=j then D*(A a d * B e f) else 0 else 0 else 0 := by
        by_cases h₁ : a=i
        · subst a
          by_cases h₂ : e=d
          · subst e
            by_cases h₃ : f=j <;> simp [h₃]
          · simp [h₂,Ne.symm h₂]
        · simp [h₁,Ne.symm h₁]
      simp_rw [step]
      simp [Matrix.mul_apply,Finset.sum_ite_irrel,Finset.mul_sum]

theorem Factors.integerScheme {b r : ℕ} (T : Factors ℚ (Fin b) (Fin r)) (hT : T.Valid) :
    ∃ S : Scheme b r, 0 < S.scale := by
  obtain ⟨L,hL,l,hl⟩ := commonDen (fun (x : Fin r × Fin b × Fin b) => T.left x.1 x.2.1 x.2.2)
  obtain ⟨R,hR,q,hq⟩ := commonDen (fun (x : Fin r × Fin b × Fin b) => T.right x.1 x.2.1 x.2.2)
  obtain ⟨O,hO,o,ho⟩ := commonDen (fun (x : Fin b × Fin b × Fin r) => T.out x.1 x.2.1 x.2.2)
  let scale : ℤ := (O:ℤ)*L*R
  obtain ⟨S,hS⟩ := schemeOfIdentities
    (fun s i j => l (s,i,j)) (fun s i j => q (s,i,j)) (fun i j s => o (i,j,s)) scale (by
      intro i j a d e f
      apply Int.cast_injective (α := ℚ)
      push_cast
      simp only [hl,hq,ho]
      calc
        _ = (O*(L*R):ℚ) * ∑ s, T.out i j s*T.left s a d*T.right s e f := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by
          rw [hT]
          by_cases h : i=a ∧ d=e ∧ f=j
          · simp [scale,h]; ring
          · simp [h])
  exact ⟨S,hS ▸ (by dsimp [scale]; positivity)⟩

/-- A fixed complex-to-number-field specialization can be descended to an
integer scheme after any tensor power, with a single d² rational-coordinate factor. -/
theorem integerPower {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (h : ℕ) :
    ∃ S : Scheme (b^h) (r^h * (Module.finrank ℚ E)^2), 0 < S.scale := by
  obtain ⟨Q,hQ⟩ := T.rational_power hT h
  exact Q.integerScheme hQ

end VWZClique.BlockMM
end

/- MMUniformRate -/
section
namespace VWZClique.BlockMM

private theorem positive_power_padding (b : ℕ) (hb : 2 ≤ b) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ, 0 < h ∧ (D:ℝ) ≤ ((b:ℝ)^h)^ε := by
  have hb' : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have ht := Real.one_lt_rpow hb' hε
  obtain ⟨h,hh⟩ := pow_unbounded_of_one_lt (D:ℝ) ht
  refine ⟨h+1,by omega,?_⟩
  have hp : (D:ℝ) ≤ ((b:ℝ)^ε)^(h+1) :=
    hh.le.trans (pow_le_pow_right₀ ht.le (by omega))
  convert! hp using 1
  rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]

/-- Rational-coordinate expansion of a fixed algebraic scheme can use arbitrarily little
slack, even if the degree of its number field is very large. -/
theorem fixed_integer_scheme {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (hb : 2 ≤ b)
    (τ : ℝ) (hr : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B R : ℕ, 2 ≤ B ∧ (R:ℝ) ≤ (B:ℝ)^(τ+ε) ∧
      ∃ S : Scheme B R, 0 < S.scale := by
  let d := Module.finrank ℚ E
  obtain ⟨h,hh,hd⟩ := positive_power_padding b hb (d^2) ε hε
  obtain ⟨S,hS⟩ := integerPower T hT h
  have hb' : 1 ≤ b := by omega
  refine ⟨b^h,r^h*d^2,?_,?_,S,hS⟩
  · exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb' (show 1 ≤ h by omega))
  · push_cast at hd ⊢
    rw [Real.rpow_add (by positivity)]
    apply mul_le_mul _ hd (by positivity) (by positivity)
    have hrh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ r) hr h
    convert! hrh using 1
    rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]

theorem scalarBudget_mono {b r R : ℕ} (h : r ≤ R) (n : ℕ) :
    scalarBudget b r n ≤ scalarBudget b R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scalarBudget]
    gcongr

/-- Matrix multiplication with a fixed positive integer scale and a single
recursion for all dimensions. Its scalar budget meets every positive slack. -/
theorem fixed_uniform {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    {b r : ℕ} (T : Factors E (Fin b) (Fin r)) (hT : T.Valid) (hb : 2 ≤ b)
    (τ : ℝ) (hτ : 2 ≤ τ) (hr : (r:ℝ) ≤ (b:ℝ)^τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B R : ℕ) (hb' : 2 ≤ B) (S : Scheme B R), 0 < S.scale ∧
      (∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ A B' : Square (Fin n), ∀ i j,
        scaled S hb' hn A B' i j / S.scale^depth B n = (A*B') i j) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (scalarBudget B R (depth B n) : ℝ) ≤ C*(n:ℝ)^(τ+ε) := by
  obtain ⟨B,R,hB,hR,S,hS⟩ := fixed_integer_scheme T hT hb τ hr (ε/2) (by linarith)
  have hB' : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hs : ((B^2 : ℕ):ℝ) ≤ (B:ℝ)^(τ+ε/2) := by
    push_cast
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hB'
      (show (2:ℝ) ≤ τ+ε/2 by linarith)
  let r' := max R (B^2)
  have hr' : (r':ℝ) ≤ (B:ℝ)^(τ+ε/2) := by
    exact_mod_cast (show (max (R:ℝ) (B^2:ℕ)) ≤ (B:ℝ)^(τ+ε/2) from max_le hR hs)
  obtain ⟨C,hC,hbudget⟩ := uniform_budget hB (show B^2 ≤ r' from le_max_right _ _)
    (τ+ε/2) (by linarith) hr' (ε/2) (by linarith)
  refine ⟨B,R,hB,S,hS,fun n hn A B' i j => scaled_div S hS.ne' hB hn A B' i j,C,hC,?_⟩
  intro n hn
  have hh := hbudget n hn
  rw [show τ+ε/2+ε/2=τ+ε by ring] at hh
  exact le_trans (by exact_mod_cast scalarBudget_mono (b := B) (le_max_left R (B^2)) (depth B n)) hh

end VWZClique.BlockMM
end

/- MMOmega -/
section
open OAI.MatrixMultiplication.Arithmetic Filter
namespace VWZClique.MM

private def price {F I : Type*} : {r : ℕ} → Program F I r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _+1, .step p g => Fin.cases g.cost (price p)

private theorem sum_price {F I : Type*} {r : ℕ} (p : Program F I r) :
    ∑ i, price p i = p.cost := by
  induction p with
  | nil => simp [Program.cost]
  | step p g ih => rw [Fin.sum_univ_succ]; simpa [price,Program.cost,add_comm] using congrArg (g.cost + ·) ih

private theorem register_kind {F I : Type*} [Field F] {r : ℕ} (p : Program F I r) (i : Fin r) :
    price p i = 1 ∨ (∃ c : F, ∀ w, p.eval w i = c) ∨ ∃ k : I, ∀ w, p.eval w i = w k := by
  induction p with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    refine Fin.cases ?_ (fun i => ih i) i
    cases g with
    | constant c => exact Or.inr (Or.inl ⟨c,fun _ => rfl⟩)
    | input k => exact Or.inr (Or.inr ⟨k,fun _ => rfl⟩)
    | _ => exact Or.inl rfl

theorem square_output_lower_bound {F : Type*} [Field F] {n : ℕ}
    (P : MatrixAlgorithm F n n n) (hc : P.Correct) : n^2 ≤ P.cost := by
  classical
  let out (ij : Fin n × Fin n) := P.output ij.1 ij.2
  have ev (ij : Fin n × Fin n) (A B : Matrix (Fin n) (Fin n) F) :
      P.program.eval (matrixInputs A B) (out ij) = (A*B) ij.1 ij.2 :=
    congrFun (congrFun (hc A B) ij.1) ij.2
  let ones : Matrix (Fin n) (Fin n) F := fun _ _ => 1
  have active (ij : Fin n × Fin n) : price P.program (out ij) = 1 := by
    rcases register_kind P.program (out ij) with h | ⟨c,h⟩ | ⟨k,h⟩
    · exact h
    · have hz := ev ij 0 0
      have ho := ev ij ones 1
      rw [h,Matrix.zero_mul] at hz
      rw [h,Matrix.mul_one] at ho
      exact (zero_ne_one ((show c = 0 from hz).symm.trans (show c=1 from ho))).elim
    · rcases k with ⟨i,j⟩ | ⟨i,j⟩
      · have he := ev ij ones 0
        rw [h,Matrix.mul_zero] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
      · have he := ev ij 0 ones
        rw [h,Matrix.zero_mul] at he
        exact (one_ne_zero (show (1:F)=0 from he)).elim
  have inject : Function.Injective out := by
    intro x y he
    by_contra hne
    let A : Matrix (Fin n) (Fin n) F := fun i j => if (i,j)=x then 1 else 0
    have hx := ev x A 1
    have hy := ev y A 1
    rw [he,hy,Matrix.mul_one] at hx
    simp [A,Ne.symm hne] at hx
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.univ.image out))
      (f := price P.program) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_image (fun _ _ _ _ h => inject h), sum_price] at hsum
  simpa [MatrixAlgorithm.cost,active,pow_two] using hsum

theorem cubic_algorithm (F : Type*) [Field F] (n : ℕ) :
    ∃ P : MatrixAlgorithm F n n n, P.Correct ∧ P.cost ≤ 2*n^3 := by
  let f := fun (v : Fin n × Fin n) (w : MatrixInput n n n → F) => ∑ k : Fin n, w (.inl (v.1,k)) * w (.inr (k,v.2))
  have build (v : Fin n × Fin n) : Circuit.Build (f v) (n*2) := by
    have h := Circuit.sum Finset.univ
      (fun k : Fin n => fun w : MatrixInput n n n → F => w (.inl (v.1,k))*w (.inr (k,v.2))) 1
      (fun k _ => Circuit.mul (Circuit.read _) (Circuit.read _))
    simpa [f] using h
  obtain ⟨r,p,out,hc,he⟩ := FoldProof.tabulate f _ build
  refine ⟨⟨r,p,fun i j => out (i,j)⟩,?_,?_⟩
  · intro A B
    ext i j
    exact he (matrixInputs A B) (i,j)
  · change p.cost ≤ _
    calc p.cost ≤ _ := hc
         _ = _ := by simp [Fintype.card_prod]; ring

theorem cubic_admissible (F : Type*) [Field F] : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2,by norm_num,?_⟩
  intro n hn
  obtain ⟨P,hc,hp⟩ := cubic_algorithm F n
  refine ⟨P,hc,?_⟩
  calc
    (P.cost : ℝ) ≤ 2*(n:ℝ)^3 := by exact_mod_cast hp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num; linarith)

theorem admissible_ge_two {F : Type*} [Field F] {τ : ℝ} (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra! h
  let ε := (2-τ)/2
  have he : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C,hC,h⟩ := hτ ε he
  have lim := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ev : ∀ᶠ n : ℕ in atTop, C < (n:ℝ)^ε := lim.eventually_gt_atTop C
  obtain ⟨n,hn,hn'⟩ := ((eventually_ge_atTop 1).and ev).exists
  obtain ⟨P,hp,hpc⟩ := h n hn
  have hb := square_output_lower_bound P hp
  have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have heq : (n:ℝ)^2 = (n:ℝ)^ε * (n:ℝ)^(τ+ε) := by
    rw [← Real.rpow_add hpos, show ε+(τ+ε)=2 by dsimp [ε]; ring]
    norm_num
  have hlow : (n:ℝ)^2 ≤ P.cost := by exact_mod_cast hb
  rw [heq] at hlow
  exact (not_lt_of_ge (hlow.trans hpc)) (mul_lt_mul_of_pos_right hn' (Real.rpow_pos_of_pos hpos _))

theorem omega_two_le (F : Type*) [Field F] : 2 ≤ omega F :=
  le_csInf ⟨3,cubic_admissible F⟩ (fun _ ht => admissible_ge_two ht)

theorem omega_admissible (F : Type*) [Field F] : AdmissibleExponent F (omega F) := by
  intro ε hε
  obtain ⟨t,ht,hlt⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | AdmissibleExponent F t})
    ⟨3,cubic_admissible F⟩ (show omega F < omega F + ε/2 by linarith)
  obtain ⟨C,hC,hP⟩ := ht (ε/2) (by linarith)
  refine ⟨C,hC,?_⟩
  intro n hn
  obtain ⟨P,hp,hpc⟩ := hP n hn
  exact ⟨P,hp,hpc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hC.le)⟩

end VWZClique.MM
end

/- BilinearExtraction -/
section
open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.BilinearExtraction

structure Semantics (F I A : Type*) where
  const : F → A
  input : I → A
  add : A → A → A
  sub : A → A → A
  mul : A → A → A

variable {F I J A B : Type*}

private def gate (m : Semantics F I A) {r : ℕ} (z : Fin r → A) : Gate F I (Fin r) → A
  | .constant c => m.const c
  | .input i => m.input i
  | .add i j => m.add (z i) (z j)
  | .sub i j => m.sub (z i) (z j)
  | .mul i j => m.mul (z i) (z j)

def run (m : Semantics F I A) : {r : ℕ} → Program F I r → Fin r → A
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gate m (run m p) g) (run m p)

private theorem simulate (m : Semantics F I A) (n : Semantics F I B) (R : A → B → Prop)
    (hc : ∀ c, R (m.const c) (n.const c)) (hi : ∀ i, R (m.input i) (n.input i))
    (ha : ∀ a b u v, R a u → R b v → R (m.add a b) (n.add u v))
    (hs : ∀ a b u v, R a u → R b v → R (m.sub a b) (n.sub u v))
    (hm : ∀ a b u v, R a u → R b v → R (m.mul a b) (n.mul u v))
    {r : ℕ} (p : Program F I r) (i : Fin r) : R (run m p i) (run n p i) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g with
    | constant c => exact hc c
    | input j => exact hi j
    | add j k => exact ha _ _ _ _ (ih j) (ih k)
    | sub j k => exact hs _ _ _ _ (ih j) (ih k)
    | mul j k => exact hm _ _ _ _ (ih j) (ih k)

variable [Field F]

abbrev Form (F I : Type*) [Field F] := (I → F) →ₗ[F] F
abbrev Term (F I J : Type*) [Field F] := Form F I × Form F J

def rankOne (s : Term F I J) (x : I → F) (y : J → F) : F := s.1 x * s.2 y

structure Jet (F I J : Type*) [Field F] where
  constant : F
  left : Form F I
  right : Form F J
  mixed : (I → F) → (J → F) → F

def jets : Semantics F (I ⊕ J) (Jet F I J) where
  const c := ⟨c,0,0,0⟩
  input := Sum.elim (fun i => ⟨0,LinearMap.proj i,0,0⟩) (fun j => ⟨0,0,LinearMap.proj j,0⟩)
  add p q := ⟨p.constant + q.constant,p.left + q.left,p.right + q.right,p.mixed + q.mixed⟩
  sub p q := ⟨p.constant - q.constant,p.left - q.left,p.right - q.right,p.mixed - q.mixed⟩
  mul p q := ⟨p.constant * q.constant, p.constant • q.left + q.constant • p.left,
    p.constant • q.right + q.constant • p.right,
    p.constant • q.mixed + q.constant • p.mixed + rankOne (p.left,q.right) + rankOne (q.left,p.right)⟩

def generated (s : Finset (Term F I J)) : Submodule F ((I→F) → (J→F) → F) :=
  Submodule.span F (Set.range fun t : s => rankOne t.val)

private theorem generated_mono {s t : Finset (Term F I J)} (h : s ⊆ t) : generated s ≤ generated t := by
  apply Submodule.span_mono
  rintro _ ⟨q,rfl⟩
  exact ⟨⟨q.val,h q.property⟩,rfl⟩

private theorem rankOne_mem {s : Finset (Term F I J)} {u : Term F I J} (hu : u ∈ s) :
    rankOne u ∈ generated s := Submodule.subset_span ⟨⟨u,hu⟩,rfl⟩

/-- A single common set of separated products spans all mixed register coefficients. -/
theorem program_span {r : ℕ} (p : Program F (I ⊕ J) r) :
    ∃ s : Finset (Term F I J), s.card ≤ 2*p.cost ∧ ∀ i, (run jets p i).mixed ∈ generated s := by
  classical
  induction p with
  | nil => exact ⟨∅,by simp [Program.cost],fun i => i.elim0⟩
  | @step r p g ih =>
    obtain ⟨s,hs,hp⟩ := ih
    have extend (t : Finset (Term F I J)) (hst : s ⊆ t) (hc : t.card ≤ 2*(p.step g).cost)
        (hnew : (gate jets (run jets p) g).mixed ∈ generated t) :
        ∃ t : Finset (Term F I J), t.card ≤ 2*(p.step g).cost ∧
          ∀ i, (run jets (p.step g) i).mixed ∈ generated t :=
      ⟨t,hc,fun i => Fin.cases hnew (fun j => generated_mono hst (hp j)) i⟩
    cases g with
    | constant c => exact extend s (by rfl) (by simpa [Program.cost,Gate.cost] using hs) (generated s).zero_mem
    | input k =>
      apply extend s (by rfl) (by simpa [Program.cost,Gate.cost] using hs)
      cases k <;> exact (generated s).zero_mem
    | add i j =>
      exact extend s (by rfl) (by simp [Program.cost,Gate.cost]; omega) ((generated s).add_mem (hp i) (hp j))
    | sub i j =>
      exact extend s (by rfl) (by simp [Program.cost,Gate.cost]; omega) ((generated s).sub_mem (hp i) (hp j))
    | mul i j =>
      let u := run jets p i
      let v := run jets p j
      let first : Term F I J := (u.left,v.right)
      let second : Term F I J := (v.left,u.right)
      let t := insert first (insert second s)
      have hst : s ⊆ t := fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      apply extend t hst
      · have h₁ := Finset.card_insert_le second s
        have h₂ := Finset.card_insert_le first (insert second s)
        simp only [t,Program.cost,Gate.cost]
        omega
      · apply (generated t).add_mem
        · apply (generated t).add_mem
          · exact (generated t).add_mem ((generated t).smul_mem _ (generated_mono hst (hp j)))
              ((generated t).smul_mem _ (generated_mono hst (hp i)))
          · exact rankOne_mem (show first ∈ t by simp [t])
        · exact rankOne_mem (show second ∈ t by simp [t])

open Polynomial
abbrev Bivar (F : Type*) [Field F] := Polynomial (Polynomial F)

noncomputable def polys (x : I → F) (y : J → F) : Semantics F (I ⊕ J) (Bivar F) :=
  ⟨fun c => C (C c), Sum.elim (fun i => C (C (x i) * X)) (fun j => C (C (y j)) * X),
   (·+·), (·-·), (·*·)⟩

def coeffAgrees (x : I → F) (y : J → F) (q : Bivar F) (z : Jet F I J) : Prop :=
  (q.coeff 0).coeff 0 = z.constant ∧ (q.coeff 0).coeff 1 = z.left x ∧
    (q.coeff 1).coeff 0 = z.right y ∧ (q.coeff 1).coeff 1 = z.mixed x y

/-- The four jet entries agree with the coefficients in the two formal scaling variables. -/
theorem program_coeff {r : ℕ} (p : Program F (I ⊕ J) r) (i : Fin r) (x : I → F) (y : J → F) :
    coeffAgrees x y (run (polys x y) p i) (run jets p i) := by
  apply simulate (polys x y) jets (coeffAgrees x y) _ _ _ _ _ p i
  · intro c; simp [coeffAgrees,polys,jets,Polynomial.coeff_C]
  · rintro (i|j) <;> simp [coeffAgrees,polys,jets,Polynomial.coeff_C]
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    simp [coeffAgrees,polys,jets,ha,hl,hr,hm,ha',hl',hr',hm']
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    simp [coeffAgrees,polys,jets,ha,hl,hr,hm,ha',hl',hr',hm']
  · rintro a b u v ⟨ha,hl,hr,hm⟩ ⟨ha',hl',hr',hm'⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      simp [polys,jets,Polynomial.mul_coeff_one,ha,hl,hr,hm,ha',hl',hr',hm',rankOne] <;> ring

private def scalars (w : I → F) : Semantics F I F := ⟨id,w,(·+·),(·-·),(·*·)⟩

private theorem run_scalars {r : ℕ} (p : Program F I r) (w : I → F) (i : Fin r) :
    run (scalars w) p i = p.eval w i := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g with
    | constant c => rfl
    | input k => rfl
    | add j k => exact congrArg₂ (·+·) (ih j) (ih k)
    | sub j k => exact congrArg₂ (·-·) (ih j) (ih k)
    | mul j k => exact congrArg₂ (·*·) (ih j) (ih k)

private noncomputable def specialize (s t : F) : Bivar F →+* F :=
  (evalRingHom t).comp (mapRingHom (evalRingHom s))

private theorem specialize_run {r : ℕ} (p : Program F (I ⊕ J) r) (i : Fin r)
    (x : I → F) (y : J → F) (s t : F) :
    specialize s t (run (polys x y) p i) =
      p.eval (Sum.elim (fun i => x i*s) (fun j => y j*t)) i := by
  rw [← run_scalars]
  apply simulate (polys x y) (scalars _) (fun p c => specialize s t p = c) _ _ _ _ _ p i
  · intro c; simp [polys,scalars,specialize]
  · rintro (i|j) <;> simp [polys,scalars,specialize]
  · intro a b u v hu hv; exact (map_add _ _ _).trans (congrArg₂ (·+·) hu hv)
  · intro a b u v hu hv; exact (map_sub _ _ _).trans (congrArg₂ (·-·) hu hv)
  · intro a b u v hu hv; exact (map_mul _ _ _).trans (congrArg₂ (·*·) hu hv)

private theorem bivar_ext [Infinite F] {p q : Bivar F}
    (h : ∀ s t : F, specialize s t p = specialize s t q) : p = q := by
  apply Polynomial.ext
  intro k
  apply Polynomial.funext
  intro s
  have hp : p.map (evalRingHom s) = q.map (evalRingHom s) := Polynomial.funext (h s)
  simpa only [coeff_map,coe_evalRingHom] using congrArg (fun z : Polynomial F => z.coeff k) hp

/-- Matrix correctness over an infinite field identifies the mixed coefficient exactly. -/
theorem matrix_mixed [Infinite F] {a b c : ℕ} (P : MatrixAlgorithm F a b c) (hP : P.Correct)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) (i : Fin a) (k : Fin c) :
    (run jets P.program (P.output i k)).mixed (fun u => A u.1 u.2) (fun v => B v.1 v.2) =
      (A*B) i k := by
  let x (u : Fin a × Fin b) := A u.1 u.2
  let y (v : Fin b × Fin c) := B v.1 v.2
  have hpoly : run (polys x y) P.program (P.output i k) = C (C ((A*B) i k) * X) * X := by
    apply bivar_ext
    intro s t
    rw [specialize_run]
    let A' : Matrix (Fin a) (Fin b) F := fun l j => A l j*s
    let B' : Matrix (Fin b) (Fin c) F := fun j l => B j l*t
    have hinput : Sum.elim (fun u => x u*s) (fun v => y v*t) = matrixInputs A' B' := by
      funext u; rcases u with ⟨_,_⟩|⟨_,_⟩ <;> rfl
    rw [hinput]
    calc
      _ = (A'*B') i k := congrFun (congrFun (hP A' B') i) k
      _ = (A*B) i k * s * t := by
        change (∑ j, (A i j*s)*(B j k*t)) = (∑ j, A i j*B j k)*s*t
        rw [Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _; ring
      _ = _ := by simp [specialize]
  have h := (program_coeff P.program (P.output i k) x y).2.2.2
  rw [hpoly] at h
  simpa [x,y] using h.symm

private theorem form_coeff [Fintype I] [DecidableEq I] (l : Form F I) (x : I → F) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  have hx : (∑ i, x i • Pi.single i (1 : F)) = x := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  calc
    l x = l (∑ i, x i • Pi.single i (1 : F)) := congrArg l hx.symm
    _ = _ := by simp [smul_eq_mul,mul_comm]

/-- The same rank-one products serve every output of a rectangular matrix program. -/
theorem matrix_algorithm [Infinite F] {a b c : ℕ} (P : MatrixAlgorithm F a b c) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧
      ∃ (U : Fin R → Fin a × Fin b → F) (V : Fin R → Fin b × Fin c → F)
        (W : Fin a → Fin c → Fin R → F),
      ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) (i : Fin a) (k : Fin c),
        (A * B) i k = ∑ q, W i k q * (∑ u, U q u * A u.1 u.2) * (∑ v, V q v * B v.1 v.2) := by
  classical
  obtain ⟨S,hS,hm⟩ := program_span P.program
  let e : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  have weights (i : Fin a) (k : Fin c) : ∃ w : S → F,
      ∑ u, w u • rankOne u.val = (run jets P.program (P.output i k)).mixed :=
    (Submodule.mem_span_range_iff_exists_fun F).mp (hm _)
  choose w hw using weights
  refine ⟨S.card,hS,fun q u => (e.symm q).val.1 (Pi.single u 1),
    fun q v => (e.symm q).val.2 (Pi.single v 1),fun i k q => w i k (e.symm q),?_⟩
  intro A B i k
  let x (u : Fin a × Fin b) := A u.1 u.2
  let y (v : Fin b × Fin c) := B v.1 v.2
  have h := congrFun (congrFun (hw i k) x) y
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,rankOne] at h
  change _ = (run jets P.program (P.output i k)).mixed (fun u => A u.1 u.2) (fun v => B v.1 v.2) at h
  rw [matrix_mixed P hP] at h
  rw [← h, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Equiv.symm_apply_apply]
  rw [form_coeff q.val.1 x,form_coeff q.val.2 y]
  exact (mul_assoc _ _ _).symm

/-- Coefficients of the matrix multiplication tensor on pairs of elementary matrices. -/
theorem matrix_structure_constants [Infinite F] {n : ℕ} (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧
      ∃ (U V : Fin R → Fin n × Fin n → F) (W : Fin n → Fin n → Fin R → F),
      ∀ i j a d e f : Fin n,
        ∑ q, W i j q * U q (a,d) * V q (e,f) = if i=a ∧ d=e ∧ f=j then 1 else 0 := by
  classical
  obtain ⟨R,hR,U,V,W,h⟩ := matrix_algorithm P hP
  refine ⟨R,hR,U,V,W,?_⟩
  intro i j a d e f
  let A : Matrix (Fin n) (Fin n) F := fun u v => if (u,v)=(a,d) then 1 else 0
  let B : Matrix (Fin n) (Fin n) F := fun u v => if (u,v)=(e,f) then 1 else 0
  have hU (q : Fin R) : (∑ u : Fin n × Fin n, U q u * A u.1 u.2) = U q (a,d) := by
    change (∑ u, U q u * (if u=(a,d) then 1 else 0)) = _
    simp [mul_ite]
  have hV (q : Fin R) : (∑ u : Fin n × Fin n, V q u * B u.1 u.2) = V q (e,f) := by
    change (∑ u, V q u * (if u=(e,f) then 1 else 0)) = _
    simp [mul_ite]
  have hm := h A B i j
  simp only [hU,hV] at hm
  rw [← hm,Matrix.mul_apply]
  by_cases hi : i=a
  · subst a
    by_cases hf : f=j
    · subst f
      simp [A,B]
      by_cases hde : d = e
      · simp [hde]
      · simp [hde,Ne.symm hde]
    · simp [A,B,hf,Ne.symm hf]
  · simp [A,B,hi]

theorem square_tables [Infinite F] {n : ℕ} (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
    ∃ R : ℕ, R ≤ 2*P.cost ∧ ∃ x : Fin 3 × Fin R × Fin n × Fin n → F,
      ∀ i j a d e f : Fin n, ∑ q, x (2,q,i,j) * x (0,q,a,d) * x (1,q,e,f) =
        if i=a ∧ d=e ∧ f=j then 1 else 0 := by
  obtain ⟨R,hR,U,V,W,h⟩ := matrix_structure_constants P hP
  let x : Fin 3 × Fin R × Fin n × Fin n → F := fun z =>
    if z.1=0 then U z.2.1 z.2.2 else if z.1=1 then V z.2.1 z.2.2 else W z.2.2.1 z.2.2.2 z.2.1
  exact ⟨R,hR,x,h⟩

end VWZClique.BilinearExtraction
end

/- CliqueSpecialize -/
section
/-! A finite list of complex constants subject to rational polynomial identities
    can be replaced by elements of one fixed number field while preserving all
    the identities. Applied to the cubic equations of bilinear multiplication,
    this preserves the base dimension and the number of products. -/

namespace VWZClique.Specialization

open MvPolynomial
noncomputable section

theorem finite_extension {σ : Type*} [Finite σ] (x : σ → ℂ) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∃ y : σ → E, ∀ p : MvPolynomial σ ℚ, aeval x p = 0 → aeval y p = 0 := by
  let I : Ideal (MvPolynomial σ ℚ) := vanishingIdeal ℚ {x}
  have hprime : I.IsPrime := by dsimp [I]; infer_instance
  have hI : I ≠ ⊤ := hprime.ne_top
  obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨z,hz⟩ := eq_vanishingIdeal_singleton_of_isMaximal (AlgebraicClosure ℚ) hJ
  let E := IntermediateField.adjoin ℚ (Set.range z)
  let y : σ → E := fun i => ⟨z i, IntermediateField.subset_adjoin ℚ (Set.range z) ⟨i,rfl⟩⟩
  have ha : ∀ a : AlgebraicClosure ℚ, IsAlgebraic ℚ a := by
    intro a
    convert! (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a using 1
  have hfinite : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => (ha a).isIntegral)
  refine ⟨E,hfinite,y,?_⟩
  have embed : E.val.comp (aeval (R := ℚ) y) = aeval z := by
    ext i
    simp [y]
  intro p hp
  have hpI : p ∈ I := (mem_vanishingIdeal_singleton_iff _ _).mpr hp
  have hh := hIJ hpI
  rw [hz, mem_vanishingIdeal_singleton_iff] at hh
  apply E.val.injective
  rw [map_zero]
  exact (DFunLike.congr_fun embed p).trans hh

abbrev Coeff (b r : ℕ) := Fin 3 × Fin r × Fin b × Fin b

/-- Coefficient identities characterizing an exact bilinear matrix product. -/
def Bilinear {F : Type*} [Field F] {b r : ℕ} (x : Coeff b r → F) : Prop :=
  ∀ i j a d e f : Fin b,
    (∑ s : Fin r, x (2,s,i,j) * x (0,s,a,d) * x (1,s,e,f)) =
      if i = a ∧ d = e ∧ f = j then 1 else 0

private def relation {b r : ℕ} (i j a d e f : Fin b) : MvPolynomial (Coeff b r) ℚ :=
  (∑ s : Fin r, X (2,s,i,j) * X (0,s,a,d) * X (1,s,e,f)) -
    if i = a ∧ d = e ∧ f = j then 1 else 0

private theorem at_relation {F : Type*} [Field F] [CharZero F] {b r : ℕ}
    (x : Coeff b r → F) (i j a d e f : Fin b) :
    aeval x (relation i j a d e f) =
      (∑ s : Fin r, x (2,s,i,j) * x (0,s,a,d) * x (1,s,e,f)) -
      (if i = a ∧ d = e ∧ f = j then 1 else 0) := by
  by_cases h : i = a ∧ d = e ∧ f = j <;> simp [relation,h]

theorem bilinear_over_number_field {b r : ℕ} {x : Coeff b r → ℂ} (hx : Bilinear x) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∃ y : Coeff b r → E, Bilinear y := by
  obtain ⟨E,hE,y,hy⟩ := finite_extension x
  refine ⟨E,hE,y,?_⟩
  intro i j a d e f
  apply sub_eq_zero.mp
  rw [← at_relation]
  apply hy
  rw [at_relation]
  exact sub_eq_zero.mpr (hx i j a d e f)

end
end VWZClique.Specialization
end

/- MMUniformBridge -/
section
open OAI.MatrixMultiplication.Arithmetic Filter
namespace VWZClique.BlockMM

/-- Any positive slack above the complex arithmetic exponent admits one fixed
positive-scale integer scheme, independent of the eventual matrix size. -/
theorem integer_uniform_at_omega (ε : ℝ) (hε : 0 < ε) :
    ∃ (B R : ℕ) (hB : 2 ≤ B) (S : Scheme B R), 0 < S.scale ∧
      (∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ A B' : Square (Fin n), ∀ i j,
        scaled S hB hn A B' i j / S.scale^depth B n = (A*B') i j) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (scalarBudget B R (depth B n) : ℝ) ≤ C*(n:ℝ)^(omega ℂ+ε) := by
  let σ := ε/3
  have hσ : 0 < σ := by dsimp [σ]; linarith
  obtain ⟨C,hC,alg⟩ := MM.omega_admissible ℂ σ hσ
  have lim := (tendsto_rpow_atTop hσ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ev : ∀ᶠ b : ℕ in atTop, 2*C < (b:ℝ)^σ := lim.eventually_gt_atTop (2*C)
  obtain ⟨b,hb,hbC⟩ := ((eventually_ge_atTop 2).and ev).exists
  obtain ⟨P,hP,hbound⟩ := alg b (by omega)
  obtain ⟨r,hr,x,hx⟩ := BilinearExtraction.square_tables P hP
  obtain ⟨E,hE,y,hy⟩ := Specialization.bilinear_over_number_field hx
  let _ := hE
  let T : Factors E (Fin b) (Fin r) :=
    ⟨fun s a d => y (0,s,a,d),fun s e f => y (1,s,e,f),fun i j s => y (2,s,i,j)⟩
  have hT : T.Valid := by
    intro i j a d e f
    have he := hy i j a d e f
    by_cases h : i=a ∧ d=e ∧ f=j <;> simpa [T,h] using he
  have hτ : 2 ≤ omega ℂ+σ+σ := by linarith [MM.omega_two_le ℂ]
  have hrate : (r:ℝ) ≤ (b:ℝ)^(omega ℂ+σ+σ) := by
    have hcast : (r:ℝ) ≤ 2*P.cost := by exact_mod_cast hr
    have hbpos : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    rw [Real.rpow_add hbpos]
    calc
      _ ≤ 2*(C*(b:ℝ)^(omega ℂ+σ)) := hcast.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))
      _ = (b:ℝ)^(omega ℂ+σ)*(2*C) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbC.le (by positivity)
  have h := fixed_uniform T hT hb (omega ℂ+σ+σ) hτ hrate σ hσ
  rwa [show omega ℂ+σ+σ+σ = omega ℂ+ε by dsimp [σ]; ring] at h

end VWZClique.BlockMM
end

/- UniformFoldBudget -/
section
namespace VWZClique.UniformFolds

/-- The entire choice of real asymptotic parameters can be discarded after
writing these 37 pairs of natural numbers to a fixed finite table. -/
noncomputable def cutoffTable : Array (ℕ × ℕ) :=
  Array.ofFn (fun i : Fin 37 => (windowAt i.val,tileAt i.val))

theorem cutoffTable_spec (H : SimpleGraph V) :
    cutoffTable.size = 37 ∧
    cutoffTable[Nat.card H.edgeSet]? =
      some (windowAt (Nat.card H.edgeSet),tileAt (Nat.card H.edgeSet)) ∧
    4 < windowAt (Nat.card H.edgeSet) ∧ 0 < tileAt (Nat.card H.edgeSet) := by
  have he : Nat.card H.edgeSet < 37 := Nat.lt_succ_of_le (edge_limit H)
  exact ⟨by simp [cutoffTable],by simp only [cutoffTable,Array.getElem?_ofFn,dif_pos he],
    (selectCut _).window_large,(selectCut _).tile_pos⟩

end VWZClique.UniformFolds
end

/- TraceDyadic -/
section
namespace VWZClique.TraceDyadic
open UniformFolds Double

variable {L : ℕ}

theorem left_cast (S T : Finset (BasisLabel L)) (K J : ℕ) (w : ChannelKey L → ℚ)
    (hw : ∀ k, Binary (w k)) (u : Node S) (v : Node T) :
    (leftTable S T K J w u v : ℚ) = (D L : ℚ)^2 *
      leftEntry S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w u v := by
  simp only [leftTable,rawLeft,transform,Int.cast_mul,Int.cast_sum,residual_cast,basis_cast,
    channel_cast w hw,leftEntry,Rat.cast_id]
  ring

theorem mid_cast (T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (v : Node T) (c : Block L) : (midTable T w v c : ℚ) = midEntry T w v c := by
  simp only [midTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,midEntry,Rat.cast_id]

theorem right_cast (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (c : Block L) (u : Node S) : (rightTable S w c u : ℚ) = rightEntry S w c u := by
  simp only [rightTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,rightEntry,Rat.cast_id]

theorem numerator_exact (S T : Finset (BasisLabel L)) (K J : ℕ)
    (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k)) :
    (numerator S T K J w : ℚ) = (D L : ℚ)^2 *
      doubleProjection S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w := by
  rw [Double.trace_identity]
  change ((∑ u : Node S, ∑ v : Node T, leftTable S T K J w u v *
    (∑ c : Block L, midTable T w v c * rightTable S w c u) : ℤ) : ℚ) = _
  simp only [Int.cast_sum,Int.cast_mul,left_cast S T K J w hw,mid_cast T w hw,right_cast S w hw]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_assoc _ _ _

end VWZClique.TraceDyadic
end

/- CliqueQuotient -/
section
/-! Exact integer division by repeated addition, comparison and subtraction, for
    recovering scaled matrix-product entries on a RAM without a divide instruction.
    This is the arithmetic schedule; the cost below counts its scalar iterations. -/

namespace VWZClique.Quotient

@[simp] theorem twice_eq (j x : ℕ) : twice j x = 2^j*x := by
  induction j generalizing x with
  | zero => simp [twice]
  | succ j ih => rw [twice,ih,pow_succ]; ring

theorem scan_correct (h a d : ℕ) (_hd : 0 < d) (ha : a < 2^h*d) :
    a = (scan h a d).1*d + (scan h a d).2 ∧ (scan h a d).2 < d := by
  induction h generalizing a with
  | zero => simpa [scan] using ha
  | succ h ih =>
    rw [pow_succ] at ha
    have htop : 2^h*2*d = 2^h*d + 2^h*d := by ring
    rw [htop] at ha
    by_cases hy : 2^h*d ≤ a
    · have hsmall : a-2^h*d < 2^h*d := by omega
      obtain ⟨he,hr⟩ := ih (a-2^h*d) hsmall
      simp only [scan,twice_eq,if_pos hy,mul_one,add_mul]
      exact ⟨by omega,hr⟩
    · simpa only [scan,twice_eq,if_neg hy] using ih a (Nat.lt_of_not_ge hy)

theorem scan_quotient (h a d : ℕ) (hd : 0 < d) (ha : a < 2^h*d) :
    (scan h a d).1 = a/d ∧ (scan h a d).2 = a%d := by
  obtain ⟨he,hr⟩ := scan_correct h a d hd ha
  constructor
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero]
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem height_cover (a p : ℕ) : a < 2^(height a p)*(p+1) := by
  induction p using height.induct a with
  | case1 p hp ih =>
    rw [height,if_pos hp,pow_add]
    norm_num
    calc
      _ < 2^height a (p+p+1)*(p+p+1+1) := ih
      _ = _ := by ring
  | case2 p hp => rw [height,if_neg hp]; simpa using Nat.lt_of_not_ge hp

theorem quotient_correct (a d : ℕ) (hd : 0 < d) :
    (quotient a d).1 = a/d ∧ (quotient a d).2 = a%d := by
  apply scan_quotient _ _ _ hd
  have h := height_cover a 0
  simp only [zero_add,mul_one] at h
  exact h.trans_le (Nat.le_mul_of_pos_right _ hd)

theorem signed_exact (z : ℤ) (d : ℕ) (hd : 0 < d) : signed (z*d) d = z := by
  unfold signed
  rw [(quotient_correct _ _ hd).1, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel _ hd]
  have hs : (d:ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hd)
  rw [Int.sign_mul, hs, mul_one, Int.sign_mul_natAbs]

end VWZClique.Quotient
end

/- UniformFoldIntegers -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

private theorem cutoff_le {K : ℕ} (hK : 4<K) (L : ℕ) :
    lower K L ≤ L ∧ width K L ≤ L := by
  have cut (j : ℕ) (hj : j ≤ 4*K) : j*L/(4*K) ≤ L :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right L hj)
  exact ⟨cut _ (by omega),(Nat.sub_le _ _).trans (cut _ (by omega))⟩

/-- The same coefficients used by the evaluator have O(L)-bit signed numerators
and a binary denominator exponent at most L. -/
theorem windowWordBounds {K : ℕ} (hK : 4<K) (L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(windowExpansion K L).coefficients i| ≤ (2:ℤ)^(3*L)) ∧
    ∀ j : BasisLabel L, ∃ e : ℕ, e ≤ L ∧ ∃ z : ℤ, |z| ≤ (2:ℤ)^(5*L+1) ∧
      (windowExpansion K L).diagonal j = Dyadic.value e z := by
  obtain ⟨hl,hw⟩ := cutoff_le hK L
  obtain ⟨coeff,diag⟩ := windowExpansion_coefficients K L
  have hs : (2:ℝ)^(lower K L)*4^(width K L) ≤ 2^(3*L) := by
    rw [show (4:ℝ) = 2^2 by norm_num,←pow_mul,←pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ht : (3:ℝ)^L ≤ 2^(2*L) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have htotal : 1+(3:ℝ)^L*(2^(lower K L)*4^(width K L)) ≤ 2^(5*L+1) := by
    calc
      _ ≤ 1+(2:ℝ)^(2*L)*2^(3*L) := by gcongr
      _ = 1+2^(5*L) := by rw [←pow_add,show 2*L+3*L=5*L by omega]
      _ ≤ (2:ℝ)^(5*L+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=5*L)]
  refine ⟨fun i => ?_,fun j => ?_⟩
  · exact_mod_cast (coeff i).trans hs
  · obtain ⟨e,he,z,hz,v⟩ := diag j
    exact ⟨e,he,z,by exact_mod_cast hz.trans htotal,v⟩

/-- This coarse bound holds even at lengths below the asymptotic rank cutoff. -/
theorem windowTerms_le (K L : ℕ) : Fintype.card (windowExpansion K L).Index ≤ 2^(3*L) := by
  change Fintype.card (Terms L (width K L)) ≤ _
  rw [terms_card]
  calc
    _ ≤ ∑ S : Finset (Fin L), 4^S.card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 5^L := by
      simpa only [one_pow,mul_one,Fintype.card_fin] using
        (Fintype.sum_pow_mul_eq_add_pow (Fin L) (4:ℕ) 1)
    _ ≤ _ := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) L

private theorem subtotal {I : Type*} [Fintype I] (s : Finset I) (f : I → ℤ)
    (m v : ℕ) (hm : Fintype.card I ≤ 2^m) (hv : ∀ i, |f i| ≤ (2:ℤ)^v) :
    |∑ i ∈ s, f i| ≤ (2:ℤ)^(m+v) := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ s, (2:ℤ)^v := Finset.sum_le_sum fun i _ => hv i
    _ = (s.card:ℤ)*(2:ℤ)^v := by simp
    _ ≤ (2:ℤ)^m * 2^v := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_univ s).trans hm) (by positivity)
    _ = _ := (pow_add _ _ _).symm

/-- Every partial one-mask sum in an evaluation on binary inputs has at most
15L bits above the unit, independently of the enumeration order. -/
theorem singleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset (windowExpansion K L).Index) (v : (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i * v i| ≤ (2:ℤ)^(15*L) := by
  have hh := (windowWordBounds hK L).1
  rw [show 15*L = 3*L+(3*L+9*L) by omega]
  apply subtotal _ _ _ _ (windowTerms_le K L)
  intro i
  rw [abs_mul,pow_add]
  exact mul_le_mul (hh i) (hv i) (abs_nonneg _) (by positivity)

/-- Arbitrary partial sums of the two-mask branch fit a signed integer
with 21L bits above the unit. -/
theorem doubleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset ((windowExpansion K L).Index × (windowExpansion K L).Index))
    (v : (windowExpansion K L).Index × (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i.1 *
      (windowExpansion K L).coefficients i.2 * v i| ≤ (2:ℤ)^(21*L) := by
  have hh := (windowWordBounds hK L).1
  have hm := windowTerms_le K L
  rw [show 21*L = (3*L+3*L) + ((3*L+3*L)+9*L) by omega]
  apply subtotal
  · rw [Fintype.card_prod,pow_add]
    exact Nat.mul_le_mul hm hm
  · intro i
    rw [abs_mul,abs_mul,pow_add,pow_add]
    exact mul_le_mul (mul_le_mul (hh i.1) (hh i.2) (abs_nonneg _) (by positivity))
      (hv i) (abs_nonneg _) (by positivity)

private theorem folded_integer {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) (d : Branch)
    (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(9*L) ∧
      placedFold (slots π H) a b ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  let r : Round L := ⟨H,π,a,b⟩
  have binary (i) : Binary (r.apply w i) := updated_binary _ _ _ _
    (r.inputs_property w Binary (Or.inr rfl) hw) i
  obtain ⟨z,hz,hv⟩ := binary_sum (child (slots π H) d) _ binary
  refine ⟨z,?_,?_⟩
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hz
    exact_mod_cast hz
  · exact (r.exact_value w d ha hb).symm.trans (by simpa only [Int.cast_natCast] using hv)

/-- The complete projected contribution is integral on every Boolean fold input,
even though its three channel matrices contain rational diagonal coefficients. -/
theorem traceProjection_integer {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(21*L+2) ∧
      traceProjection L (windowExpansion K L) ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  classical
  let q := windowExpansion K L
  let E := slots π H
  let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
  choose left leftBound leftVal using
    fun i : q.Index => folded_integer H π w hw .left (some (q.masks i)) none rfl rfl
  choose right rightBound rightVal using
    fun j : q.Index => folded_integer H π w hw .right none (some (q.masks j)) rfl rfl
  choose both bothBound bothVal using fun ij : q.Index × q.Index =>
    folded_integer H π w hw .both (some (q.masks ij.1)) (some (q.masks ij.2)) rfl rfl
  let A : ℤ := ∑ i, q.coefficients i * left i
  let B : ℤ := ∑ j, q.coefficients j * right j
  let D : ℤ := ∑ ij : q.Index × q.Index, (q.coefficients ij.1 * q.coefficients ij.2) * both ij
  have ha : |A| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ left leftBound
  have hb : |B| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ right rightBound
  have hd : |D| ≤ (2:ℤ)^(21*L) := doubleSubtotal hK L Finset.univ both bothBound
  have la : ∑ i, (q.coefficients i:ℚ)*placedFold E (some (q.masks i)) none u = (A:ℚ) := by
    simp only [A,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg _ (leftVal i))
  have lb : ∑ j, (q.coefficients j:ℚ)*placedFold E none (some (q.masks j)) u = (B:ℚ) := by
    simp only [B,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg _ (rightVal j))
  have ld : ∑ i, ∑ j, ((q.coefficients i:ℚ)*(q.coefficients j:ℚ))*
      placedFold E (some (q.masks i)) (some (q.masks j)) u = (D:ℚ) := by
    simp only [D,Int.cast_sum,Int.cast_mul,Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => congrArg _ (bothVal (i,j))))
  obtain ⟨v,hv,value⟩ := binary_sum H w hw
  have hval : placedFold E none none u = (v:ℚ) := (input_exact π H w).trans value
  have h := q.decompose E u (input_supported (Round.mk H π none none) w)
  rw [la,lb,ld,hval] at h
  let P : ℤ := (2:ℤ)^(21*L)
  have h15 : (2:ℤ)^(15*L) ≤ P := pow_le_pow_right₀ (by norm_num) (by omega)
  have hv' : |(v:ℤ)| ≤ P := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hv
    exact (by exact_mod_cast hv : (v:ℤ) ≤ 2^(9*L)).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨(v:ℤ)-A-B+D,?_,?_⟩
  · calc
      _ ≤ |(v:ℤ)-A-B|+|D| := abs_add_le _ _
      _ ≤ (|(v:ℤ)-A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ (|(v:ℤ)|+|A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ P+P+P+P := add_le_add (add_le_add (add_le_add hv' (ha.trans h15)) (hb.trans h15)) hd
      _ = _ := by rw [pow_add]; dsimp [P]; ring
  · rw [traceProjection_correct]
    push_cast
    linarith

/-- On every actual graph call the integer trace numerator is divisible by the
common binary denominator. The signed shift/subtract quotient returns exactly the
projected contribution. -/
theorem traceIntegerQuotient {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    let q := windowExpansion K L
    let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
    let z := TraceDyadic.numerator q.labels q.labels K K u
    let d : ℕ := (2^L)^2
    (d:ℤ) ∣ z ∧ (Quotient.signed z d:ℚ) = traceProjection L q u ∧
      |Quotient.signed z d| ≤ (2:ℤ)^(21*L+2) := by
  intro q u z d
  obtain ⟨v,hv,he⟩ := traceProjection_integer hK L H π w hw
  have hb (i) : Binary (u i) :=
    (Round.mk H π (none : Option (Mask L)) none).inputs_property w Binary (Or.inr rfl) hw i
  have hx := TraceDyadic.numerator_exact q.labels q.labels K K u hb
  have he' : doubleProjection q.labels q.labels q.diagonal q.diagonal u = (v:ℚ) :=
    (traceProjection_correct q u).symm.trans he
  have eq : z = v*(d:ℤ) := by
    have h : (z:ℚ) = ((v*(d:ℤ):ℤ):ℚ) := by
      rw [show (z:ℚ) = (TraceDyadic.D L : ℚ)^2 *
        doubleProjection q.labels q.labels q.diagonal q.diagonal u from hx,he']
      simp [d,TraceDyadic.D,mul_comm]
    exact_mod_cast h
  have hd : 0<d := by dsimp [d]; positivity
  have res : Quotient.signed z d = v := by rw [eq,Quotient.signed_exact _ _ hd]
  exact ⟨⟨v,eq.trans (mul_comm _ _)⟩,res ▸ he.symm,res ▸ hv⟩

end VWZClique.UniformFolds
end

/- NativeProjectionValue -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds NativeFrame

def finalize (d : ℕ) := Command.seq normalize (install d)

theorem rawTrace_fact {K : ℕ} (hK : 4<K) (L : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    let num := TraceDyadic.numerator (windowExpansion K L).labels (windowExpansion K L).labels K K
      ((Round.mk H π (none : Option (Mask L)) none).inputs w)
    num=((2:ℤ)^L)^2*integerTrace K L H π w ∧ |integerTrace K L H π w|≤(2:ℤ)^(21*L+2) := by
  intro num
  let d : ℕ := (2^L)^2
  have data := traceIntegerQuotient hK L H π w hw
  change (d:ℤ) ∣ num ∧ _ ∧ |Quotient.signed num d|≤(2:ℤ)^(21*L+2) at data
  change num=((2:ℤ)^L)^2*Quotient.signed num d ∧ |Quotient.signed num d|≤(2:ℤ)^(21*L+2)
  obtain ⟨⟨v,eq⟩,_,bound⟩ := data
  refine ⟨?_,bound⟩
  have ev : num=v*d := eq.trans (mul_comm _ _)
  rw [show Quotient.signed num d=v by rw [ev,Quotient.signed_exact _ _ (by dsimp [d];positivity)]]
  simpa [d] using eq

/-- Consume the exact projected-product output, divide out the common
scheme and dyadic scales, and install all five physical cursor headers. -/
theorem finalize_runs {W L c b s base d count M K : ℕ} (hc : 0<c) (hb : 2≤b) (size : s≤(2^L)^3)
    (hK : 4<K) (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L)→ℚ) (hw : ∀ j, Binary (w j))
    (cap : Graph.Division.Room W (normalizeRoom c L)) (addrRoom : Graph.Division.Room W M)
    (space : countAddr base (2^L)≤M) (m : Memory) (dim : m 0=((2^L:ℕ):ℤ)) (len : m 320=L)
    (weights : m (reg d .weights)=base) (cnt : m (countAddr base (2^L):ℤ)=count)
    (output : m rawTrace=(commonScale c b L s:ℤ)*TraceDyadic.numerator (windowExpansion K L).labels
      (windowExpansion K L).labels K K ((Round.mk H π (none : Option (Mask L)) none).inputs w))
    (sc : m scaleReg=(commonScale c b L s:ℤ)) :
    ∃ f o, f≤13*(21*L+3)+44 ∧ Runs W (finalize d) m f o ∧
      Installed d count (integerTrace K L H π w) o ∧ ∀ j : ℤ, 0≤j → off d j → o j=m j := by
  obtain ⟨fact,bound⟩ := rawTrace_fact hK L H π w hw
  have raw : m rawTrace=(commonScale c b L s:ℤ)*((2:ℤ)^L)^2*integerTrace K L H π w := by rw [output,fact];ring
  obtain ⟨t,x,ht,norm,ans,keep⟩ := normalize_runs hc hb size cap m _ bound raw sc dim len
  have same (j : ℤ) (hi : 0≤j) : x j=m j := by obtain ⟨u,rfl⟩ := Int.eq_ofNat_of_zero_le hi;exact keep u
  obtain ⟨o,frames,fields,frame⟩ := install_runs addrRoom space x ((keep 0).trans dim)
    ((same _ (reg_positive d .weights).le).trans weights) ((keep _).trans cnt) _ ans
  exact ⟨_,o,by omega,.seq norm frames,fields,fun j pos h => (frame _ pos h).trans (same _ pos)⟩

end VWZClique.IntegerRAM.Projected
end

/- NativeFrameStack -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

/-- Sufficient capacity per depth, including the last row of every edge table. -/
def Capacity (lay : StackLayout) (L : ℕ) := ∀ d,
  lay.base d + 9*(2^L) + 81*(2^L*2^L) ≤ lay.base (d+1)

theorem capacity_mono {lay : StackLayout} {L} (cap : Capacity lay L) : Monotone lay.base :=
  monotone_nat_of_le_succ fun d => by have := cap d; omega

theorem weights_region {L : ℕ} {lay : StackLayout} (cap : Capacity lay L) {d w} {m o : Memory}
    (src : @Weights L lay d w m) (ptr : o (reg d .weights)=m (reg d .weights))
    (fr : ∀ a : ℕ, lay.base d ≤ a → a < lay.base (d+1) → o a=m a) : Weights lay d w o := by
  refine ⟨ptr.trans src.1,?_⟩
  intro i
  have hl := NativeLeaf.index_lt i
  have hb := cap d
  exact (congrArg (Int.cast : ℤ → ℚ) (fr _ (Nat.le_add_right _ _) (by omega))).trans (src.2 i)

/-- Writes to a child arena, deeper scratch, or the stable temporary bank do
not disturb suspended ancestors. Only the live positive prefix of the tables
and the explicit ancestor register cells need be preserved. -/
theorem saved_before {L} (lay : StackLayout) (cap : Capacity lay L) (d : ℕ) (q : List (NativeTraversal.Slot L))
    {m o : Memory} (tables : ∀ a : ℕ, 512 ≤ a → a < lay.base d → o a=m a)
    (regs : ∀ i<d, ∀ f, o (reg i f)=m (reg i f)) (src : Saved lay d q m) :
    Saved lay d q o := by
  induction q generalizing d with
  | nil => trivial
  | cons h rest ih =>
    obtain ⟨lt,ok,arm,tail⟩ := src
    let j := depthOf h
    have gj : lay.base (j+1) ≤ lay.base d := capacity_mono cap lt
    have inside (a : ℕ) (ha : lay.base j ≤ a) (hb : a < lay.base (j+1)) :=
      tables a ((lay.large j).trans ha) (hb.trans_le gj)
    have savedTail := ih j (fun a ha hb => tables a ha (hb.trans_le (capacity_mono cap lt.le)))
      (fun k hk f => regs k (hk.trans lt) f) tail
    refine ⟨lt,?_,?_,savedTail⟩
    · cases h with
      | input k w => exact weights_region cap ok (regs k lt _) inside
      | value k z => exact (regs k lt _).trans ok
      | cursor k H π b w i z =>
        obtain ⟨wt,p,l,idx,v⟩ := ok
        exact ⟨weights_region cap wt (regs k lt _) inside,lay.transfer k H m o inside p,
          fun e => (regs k lt _).trans (l e),(regs k lt _).trans idx,(regs k lt _).trans v⟩
    · cases h with
      | input => exact False.elim arm
      | value => exact False.elim arm
      | cursor k H π b w i z =>
        obtain ⟨hi,hc⟩ := arm
        exact ⟨hi,(regs k lt _).trans hc⟩

/-- Projection may freely write its own arena after the weight table. -/
theorem project_repr {L} (lay : StackLayout) (cap : Capacity lay L) {d H π w}
    (q : List (NativeTraversal.Slot L)) {m o : Memory} {z : ℤ}
    (src : Repr lay (.input d w::q) m) (globals : Globals L lay o)
    (older : ∀ a : ℕ, 512≤a → a<lay.base d → o a=m a)
    (hdr : ∀ j<d, ∀ f, o (reg j f)=m (reg j f))
    (wt : Weights lay d w o) (prep : lay.prepared d H o)
    (len : ∀ b, o (reg d (lengthField b))=visits (number L H) b)
    (ix : o (reg d .index)=0) (val : o (reg d .value)=z) :
    Repr lay (.cursor d H π .left w 0 z::q) o :=
  ⟨globals,⟨wt,prep,len,by simpa using ix,val⟩,saved_before lay cap d q older hdr src.2.2⟩

end VWZClique.IntegerRAM.NativeFrame
end

/- NativeProjectionFinalize -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds NativeFrame NativeTraversal

/-- The caller supplies the native trace accumulator, the common scale, and
the compact table produced in this frame. The result satisfies the saved
recursive-stack invariant on the first mask visit. -/
theorem finalize_repr {L W c b s M d : ℕ} (hc : 0<c) (hb : 2≤b) (size : s≤(2^L)^3)
    (lay : StackLayout) (space : Capacity lay L) (hd : d≤36)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L)→ℚ) (hw : ∀ j, Binary (w j))
    (q : List (NativeTraversal.Slot L)) {orig m : Memory} (src : Repr lay (.input d w::q) orig)
    (glob : Globals L lay m) (older : ∀ a : ℕ, 512≤a → a<lay.base d → m a=orig a)
    (hdr : ∀ j<d, ∀ f, m (reg j f)=orig (reg j f)) (weights : Weights lay d w m)
    (ready : lay.prepared d H m) (cnt : m (countAddr (lay.base d) (2^L):ℤ)=number L H)
    (cap : Graph.Division.Room W (normalizeRoom c L)) (addrRoom : Graph.Division.Room W M)
    (addr : countAddr (lay.base d) (2^L)≤M)
    (output : m rawTrace=(commonScale c b L s:ℤ)*
      TraceDyadic.numerator (qOf H L).labels (qOf H L).labels (windowAt (Nat.card H.edgeSet))
        (windowAt (Nat.card H.edgeSet)) ((Round.mk H π (none : Option (Mask L)) none).inputs w))
    (sc : m scaleReg=(commonScale c b L s:ℤ)) :
    ∃ f o, f≤13*(21*L+3)+44 ∧ Runs W (finalize d) m f o ∧
      Repr lay (.cursor d H π .left w 0 (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::q) o := by
  obtain ⟨f,o,hf,run,fields,frame⟩ := finalize_runs hc hb size (cutoffTable_spec H).2.2.1 H π w hw cap addrRoom addr
    m glob.dim glob.length weights.1 cnt output sc
  have top (j : ℕ) (hj : 297≤j) : o j=m j := by
    apply frame _ (by omega)
    have sep (s : Field) : (j:ℤ)≠reg d s := by have := reg_below hd s;omega
    exact ⟨sep _,sep _,sep _,sep _,sep _⟩
  have zero : o 0=m 0 := frame 0 (by decide)
    ⟨(reg_positive d _).ne,(reg_positive d _).ne,(reg_positive d _).ne,(reg_positive d _).ne,(reg_positive d _).ne⟩
  have wreg : o (reg d .weights)=m (reg d .weights) := frame _ (reg_positive d _).le
    ⟨different _ (by decide),different _ (by decide),different _ (by decide),different _ (by decide),different _ (by decide)⟩
  refine ⟨f,o,hf,run,project_repr lay space q src (glob.transfer zero (top 320 (by decide)) (top 321 (by decide)))
    (fun j h₁ h₂ => (top _ (by omega)).trans (older _ h₁ h₂)) ?_ (weights_transfer weights wreg top)
    (lay.transferAll _ _ _ _ top ready) ?_ fields.index fields.value⟩
  · intro j hj f
    have sep (g : Field) := (separate hj f g).ne
    exact (frame _ (reg_positive _ _).le ⟨sep _,sep _,sep _,sep _,sep _⟩).trans (hdr _ hj _)
  · intro branch;cases branch
    · exact fields.first
    · exact fields.second
    · exact fields.both

end VWZClique.IntegerRAM.Projected
end

/- NativeArenaLayout -/
section
namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame NativeTraversal UniformFolds BlockReduction MaskScan.Arena

theorem layoutCapacity (L root output : ℕ) (start : 512≤root) : @NativeFrame.Capacity (layout L root output start) L := by
  intro d
  change atDepth root (2^L) d + 9*2^L + 81*(2^L*2^L) ≤ child (atDepth root (2^L) d) (2^L)
  dsimp [child,rows,maps,metaBase,tableWords]
  omega

end VWZClique.IntegerRAM.NativeArena
end

/- NativeProjectionArena -/
section
namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds NativeFrame NativeTraversal NativeArena

theorem finalize_in_arena {L W c b s M d root outputAddr : ℕ} (start : 512≤root)
    (hc : 0<c) (hb : 2≤b) (size : s≤(2^L)^3) (hd : d≤36)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L)→ℚ) (hw : ∀ j, Binary (w j))
    (q : List (NativeTraversal.Slot L)) {orig m : Memory}
    (src : Repr (layout L root outputAddr start) (.input d w::q) orig)
    (ready : MaskScan.Arena.Prepared L (windowAt (Nat.card H.edgeSet)) (atDepth root (2^L) d) m)
    (prior : ∀ j : ℕ, projectionPrefix (atDepth root (2^L) d) (2^L) j → m j=orig j)
    (cap : Graph.Division.Room W (normalizeRoom c L)) (addrRoom : Graph.Division.Room W M)
    (addr : countAddr (atDepth root (2^L) d) (2^L)≤M)
    (scaled : m rawTrace=(commonScale c b L s:ℤ)*
      TraceDyadic.numerator (qOf H L).labels (qOf H L).labels (windowAt (Nat.card H.edgeSet))
        (windowAt (Nat.card H.edgeSet)) ((Round.mk H π (none : Option (Mask L)) none).inputs w))
    (sc : m scaleReg=(commonScale c b L s:ℤ)) :
    ∃ f o, f≤13*(21*L+3)+44 ∧ Runs W (finalize d) m f o ∧
      Repr (layout L root outputAddr start) (.cursor d H π .left w 0
        (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::q) o := by
  let lay := layout L root outputAddr start
  let n := 2^L
  let base := atDepth root n d
  have before (j : ℕ) (low : 512≤j) (high : j < metaBase base n) : m j=orig j :=
    prior j (Or.inr (Or.inr (Or.inr ⟨low,high⟩)))
  have head (i : ℕ) (hi : i≤36) (f : Field) : m (reg i f)=orig (reg i f) := by
    have p := (reg_positive i f).le
    obtain ⟨a,e⟩ := Int.eq_ofNat_of_zero_le p
    rw [e];apply prior a;apply Or.inl
    have lt := reg_below hi f;rw [e] at lt;exact_mod_cast lt
  have wt : Weights lay d w m := by
    refine ⟨(head _ hd _).trans src.2.1.1,?_⟩
    intro j
    have lt := NativeLeaf.index_lt j
    have hi : base+Graph.Table.wordIndex j < metaBase base n := by exact Nat.add_lt_add_left lt base
    have low : 512≤base := lay.large d
    exact (congrArg (Int.cast : ℤ→ℚ) (before _ (by omega) hi)).trans (src.2.1.2 j)
  have gl : Globals L lay m := src.1.transfer (prior 0 (Or.inl (by decide)))
    (prior 320 (Or.inr (Or.inl rfl))) (prior 321 (Or.inr (Or.inr (Or.inl rfl))))
  have ct : m (countAddr base n:ℤ)=number L H := by
    have eq : countAddr base n=MaskScan.Arena.slot base n 7 := by simp [countAddr,MaskScan.Arena.slot,MaskScan.Arena.origin,MaskScan.Arena.span,pow_two]
    rw [eq];exact ready.maskCount
  apply finalize_repr hc hb size lay (layoutCapacity L root outputAddr start) hd H π w hw q src gl _ _ wt ready ct cap addrRoom addr scaled sc
  · intro j low high;apply before j low
    change j<base at high;unfold metaBase;omega
  · intro i hi f;exact head i (by omega) f

end VWZClique.IntegerRAM.Projected
end

/- NativeProjectionWorkspace -/
section
namespace VWZClique.IntegerRAM.Projected.Workspace

theorem table_sizes {n a s t : ℕ} (ha : a ≤ n^2) (hs : s ≤ n^3) (ht : t*s=n^3) :
    (a*n)*(a*n) ≤ n^6 ∧ (a*n)*n^3 ≤ n^6 ∧ a*n^4 ≤ n^6 ∧ s*s ≤ n^6 ∧ t*(s*s) ≤ n^6 := by
  have han : a*n ≤ n^3 := by simpa only [pow_succ] using Nat.mul_le_mul_right n ha
  have n3 : n^3*n^3=n^6 := (pow_add _ 3 3).symm
  refine ⟨(Nat.mul_le_mul han han).trans_eq n3,(Nat.mul_le_mul_right _ han).trans_eq n3,
    (Nat.mul_le_mul_right _ ha).trans_eq ((pow_add _ 2 4).symm),
    (Nat.mul_le_mul hs hs).trans_eq n3,?_⟩
  rw [←Nat.mul_assoc,ht]; exact (Nat.mul_le_mul_left _ hs).trans_eq n3

theorem end_bound (start n : ℕ) (hn : 1 ≤ n) : (banks start n).output+n^6 ≤ start+12*n^6 := by
  have h : n^3 ≤ n^6 := Nat.pow_le_pow_right hn (by decide)
  simp [banks]; omega

end VWZClique.IntegerRAM.Projected.Workspace
end

/- WordButterflyTiming -/
section
/-! Minimum fuel in the machine interpreter, including all native setup, buffer
    passes, branches, and acceptance. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

/-- Uniform constant in the O((L+1)4^L) bound, including length zero. -/
theorem dense_budget (l : ℕ) :
    18+4*(l-1)+l*(15+20*4^(l-1)) ≤ 57*(l+1)*4^l := by
  let n := (4:ℕ)^l
  have h : 4^(l-1) ≤ n := Nat.pow_le_pow_right (by decide) (by omega)
  have hn : 1≤n := Nat.one_le_pow _ _ (by decide)
  have hl : l ≤ l*n := by simpa using Nat.mul_le_mul_left l hn
  have hs := Nat.mul_le_mul_left l h
  change _ ≤ 57*(l+1)*n
  nlinarith [Nat.sub_le l 1]

end VWZClique.IntegerRAM.Butterfly
end

/- NativeProjectionPrepare -/
section
namespace VWZClique.IntegerRAM.Projected.Preparation
open Structured UniformFolds NativeFrame NativeTraversal NativeArena BlockMM

def coefficient (d K b c : ℕ) :=
  1200+30*K+headerTime d+SupportDP.constant+41+SquareCode.Layout.padSteps b c

theorem ticks_bound (d K b c L : ℕ) : ticks d K b c L≤ coefficient d K b c*(2^L)^5 := by
  let n := 2^L
  have s : L+1≤ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=L))
  have p : 1≤ n := Nat.one_le_pow _ _ (by decide)
  have nle : n≤ n^5 := by simpa only [pow_one] using Nat.pow_le_pow_right p (by decide : 1≤5)
  have cst : headerTime d≤ headerTime d*n^5 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (headerTime d) (p.trans nle)
  have paid := Nat.mul_le_mul_right (SquareCode.Layout.padSteps b c) (s.trans nle)
  unfold ticks coefficient;change _≤_*n^5
  change (1200+30*K)*n^5+headerTime d+(SupportDP.constant+35)*n^5+(6+(L+1)*SquareCode.Layout.padSteps b c) ≤ _
  nlinarith only [cst,paid,p,nle]

end VWZClique.IntegerRAM.Projected.Preparation
end

/- NativeSquareCatalog -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

theorem grid_cost_bound {N D : ℕ} (hn : 1 ≤ N) (hd : 1 ≤ D) (B : ℕ) :
    gridCost N D B ≤ (B+15)*(N*D*D) := by
  have hD : N ≤ N*D := by simpa using Nat.mul_le_mul_left N hd
  have hD' : N*D ≤ N*D*D := by simpa using Nat.mul_le_mul_left (N*D) hd
  unfold gridCost
  ring_nf at hD hD' ⊢
  omega

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareAscent -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

private theorem listRate {I : Type*} (l : List I) (cost : I → ℕ) {N D : ℕ} (hn : 1 ≤ N) (hd : 1 ≤ D) :
    (l.map (fun j => gridCost N D (cost j))).sum ≤ (l.map (fun j => cost j+15)).sum*(N*D*D) := by
  induction l with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Nat.add_mul]
    exact Nat.add_le_add (grid_cost_bound hn hd _) ih

/-- Native instruction count for an entire downward or upward layer, with one
constant independent of the number of nodes and their matrix dimensions. -/
theorem layer_time {b r : ℕ} (S : Scheme b r) :
    ∃ C : ℕ, ∀ N D : ℕ, 0 < N → 0 < D →
      ((all (Fin 3 × Fin r)).map (fun j => gridCost N D (downBatchCost S j))).sum
      + ((all (Fin b × Fin b)).map (fun j => gridCost N D (upBatchCost S j))).sum ≤ C*(N*D*D) := by
  let left := ((all (Fin 3 × Fin r)).map (fun j => downBatchCost S j+15)).sum
  let right := ((all (Fin b × Fin b)).map (fun j => upBatchCost S j+15)).sum
  refine ⟨left+right,?_⟩
  intro N D hn hd
  rw [Nat.add_mul]
  exact Nat.add_le_add (listRate _ _ hn hd) (listRate _ _ hn hd)

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- MMWordLayoutRate -/
section
open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.BlockMM.WordLayout

theorem rank_pos {b r : ℕ} (S : Scheme b r) (hb : 0<b) (hs : 0<S.scale) : 0<r := by
  by_contra! h
  obtain rfl : r=0 := by omega
  let i : Fin b := ⟨0,hb⟩
  have he := S.correct (1 : Square (Fin b)) 1 i i
  simp at he
  omega

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareRate -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

/-- Sum the actual instruction charges over all levels of the rank-r tree. -/
theorem charge_bound {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0 < r) :
    ∃ C : ℕ, ∀ h N : ℕ, 0 < N → charge S h N ≤ C*N*scalarBudget b r h := by
  obtain ⟨P,hP⟩ := layer_time S
  let K := (Expr.num b).steps+(Expr.num r).steps+downAdjTime b r+(back b).steps+(parentSide b).steps+
    downTest.steps+upTest.steps+50
  let C := P+K+leafBodySteps+20
  refine ⟨C,?_⟩
  intro h
  induction h with
  | zero =>
    intro N hn
    simp only [charge,scalarBudget,Nat.mul_one]
    have H := Nat.mul_le_mul_right N (show leafBodySteps+5 ≤ C by dsimp [C]; omega)
    rw [Nat.add_mul] at H
    rw [Nat.mul_add]
    nlinarith
  | succ h ih =>
    intro N hn
    let D := b^h
    have hd : 0 < D := Nat.pow_pos (by omega)
    have hp := hP N D hn hd
    have old := ih (N*r) (Nat.mul_pos hn hr)
    have hnD : N ≤ N*D := by simpa using Nat.mul_le_mul_left N hd
    have hD : D ≤ N*D := by simpa using Nat.mul_le_mul_right D hn
    have hdD : N*D ≤ N*D*D := by simpa using Nat.mul_le_mul_left (N*D) hd
    have oneD : 1 ≤ N*D*D := (show 1 ≤ N from hn).trans (hnD.trans hdD)
    have costK : K ≤ K*(N*D*D) := by simpa using Nat.mul_le_mul_left K oneD
    have extra : 5*N+5*D ≤ 10*(N*D*D) := by omega
    have eqPow : (b^2)^h=D*D := by dsimp [D]; rw [←mul_pow,pow_two]
    have cb : P+K+10 ≤ C := by dsimp [C]; omega
    have blow : 1 ≤ 6*r*b^2 := by change 0 < 6*r*b^2; positivity
    let L := ((all (Fin 3 × Fin r)).map (fun j => gridCost N D (downBatchCost S j))).sum
    let R := ((all (Fin b × Fin b)).map (fun j => gridCost N D (upBatchCost S j))).sum
    have sumP : L+R ≤ P*(N*D*D) := hp
    have fixed : downTime S h N + (downTest.steps+3) + upTime S h N + (upTest.steps+3) ≤ L+R+K+(5*N+5*D) := by
      dsimp only [downTime,upTime,quotTime,K,L,R,D]
      omega
    have chargeLocal := fixed.trans (Nat.add_le_add (Nat.add_le_add sumP costK) extra)
    have local' : downTime S h N + (downTest.steps+3) + upTime S h N + (upTest.steps+3) ≤ C*(N*D*D) := by
      have bound := Nat.mul_le_mul_right (N*D*D) cb
      rw [Nat.add_mul,Nat.add_mul] at bound
      exact chargeLocal.trans bound
    have higher := Nat.mul_le_mul_left (C*(N*D*D)) blow
    simp only [Nat.mul_one] at higher
    calc
      _ = charge S h (N*r)+(downTime S h N+(downTest.steps+3)+upTime S h N+(upTest.steps+3)) := by rw [charge]; omega
      _ ≤ C*(N*r)*scalarBudget b r h + C*(N*D*D)*(6*r*b^2) :=
        Nat.add_le_add old (local'.trans higher)
      _ = _ := by rw [scalarBudget,eqPow]; ring

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareMultiplyRate -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

def Job.factor (q : Job) := setupCost q.setup+(tileSteps q.copy+15)

theorem Job.cost_le (q : Job) (a : Anchors) (hn : 0<a.raw) (h : a.raw ≤ a.pad) :
    q.cost a ≤ q.factor*(a.pad*a.pad) := by
  have hd : 0 < q.dim.val a := by cases x : q.dim <;> simp [Width.val] <;> omega
  have bound : q.dim.val a ≤ a.pad := by cases x : q.dim <;> simp [Width.val] <;> omega
  have e := grid_cost_bound (N:=1) le_rfl hd (tileSteps q.copy)
  simp only [Nat.one_mul] at e
  have both := Nat.mul_le_mul bound bound
  have posSq : 1 ≤ a.pad*a.pad := Nat.mul_pos (by omega) (by omega)
  have fixed := Nat.mul_le_mul_left (setupCost q.setup) posSq
  simp only [Nat.mul_one] at fixed
  rw [Job.factor,Nat.add_mul]
  exact Nat.add_le_add fixed (e.trans (Nat.mul_le_mul_left _ both))

theorem runtime_le {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0<r) :
    ∃ P Q : ℕ, ∀ a : Anchors, 1 ≤ a.raw → a.pad=b^(depth b a.raw) →
      runtimeCost S a ≤ P*scalarBudget b r (depth b a.raw) + Q*(a.raw*a.raw) := by
  obtain ⟨P,hP⟩ := charge_bound S hb hr
  let fixed := 2+setupCost chooseArea+setupCost pointCore+4
  let coeff := fixed+padSteps b S.scale+(fillBank 0).factor+(copyInto .left 0).factor+
    (fillBank 1).factor+(copyInto .right 1).factor+emitJob.factor
  refine ⟨P,coeff*(b*b),?_⟩
  intro a hn dim
  have rawPad : a.raw ≤ a.pad := dim ▸ (depth_bounds hb hn).1
  have padMax : a.pad ≤ b*a.raw := dim ▸ (depth_bounds hb hn).2
  have depthPow (j : ℕ) : j ≤ b^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have pos : 0 < b^j := Nat.pow_pos (by omega)
      rw [pow_succ]; nlinarith
  have depPad : depth b a.raw ≤ a.pad := dim ▸ depthPow _
  have posSq : 1 ≤ a.pad*a.pad := Nat.mul_pos (by omega) (by omega)
  have pp : a.pad ≤ a.pad*a.pad := by simpa using Nat.mul_le_mul_left a.pad (show 1 ≤ a.pad by omega)
  have d := Nat.mul_le_mul_right (padSteps b S.scale) (depPad.trans pp)
  have f := Nat.mul_le_mul_left fixed posSq
  simp only [Nat.mul_one] at f
  have l := (fillBank 0).cost_le a hn rawPad
  have l' := (copyInto .left 0).cost_le a hn rawPad
  have rhsFill := (fillBank 1).cost_le a hn rawPad
  have rhsCopy := (copyInto .right 1).cost_le a hn rawPad
  have u := emitJob.cost_le a hn rawPad
  have charge := hP (depth b a.raw) 1 (by decide)
  simp only [Nat.mul_one] at charge
  have padBound : coeff*(a.pad*a.pad) ≤ (coeff*(b*b))*(a.raw*a.raw) := by
    exact (Nat.mul_le_mul_left coeff (Nat.mul_le_mul padMax padMax)).trans_eq (by ring)
  apply (show runtimeCost S a ≤ P*scalarBudget b r (depth b a.raw) + coeff*(a.pad*a.pad) from ?_).trans
    (Nat.add_le_add_left padBound _)
  simp only [runtimeCost,coeff,Nat.add_mul]
  rw [Nat.mul_comm (depth b a.raw)] 
  rw [Nat.mul_comm (depth b a.raw)] at d
  rw [Nat.mul_comm (a.pad*a.pad) (padSteps b S.scale)] at d
  dsimp only [fixed] at f ⊢
  omega

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareSpace -/
section
namespace VWZClique.BlockMM.WordLayout

/-- The packed matrix calling convention has polynomial peak space for every
fixed scheme, without putting a restriction on its rank. -/
theorem polynomial_space {b r : ℕ} (hb : 2 ≤ b) :
    ∃ C d : ℕ, ∀ n : ℕ, 1 ≤ n → space b r (depth b n) 1 ≤ C*n^d := by
  let B := b*b+r+3
  have sq : b*b ≤ B := by dsimp [B]; omega
  have cap : 3+r ≤ B := by dsimp [B]; omega
  have batch (h N : ℕ) : space b r h N ≤ N*B^(h+1) := by
    induction h generalizing N with
    | zero =>
      simp only [space,size,plane,pow_zero,Nat.mul_one,Nat.zero_add,pow_one]
      exact (Nat.mul_comm 3 N).le.trans (Nat.mul_le_mul_left N (show 3 ≤ B by omega))
    | succ j ih =>
      have dd : b^(j+1)*b^(j+1) ≤ B^(j+1) := by
        rw [←mul_pow]; exact Nat.pow_le_pow_left sq _
      have parent := Nat.mul_le_mul_left (3*N) dd
      have child := ih (N*r)
      have larger := Nat.mul_le_mul_right (N*B^(j+1)) cap
      calc
        space b r (j+1) N = 3*N*(b^(j+1)*b^(j+1))+space b r j (N*r) := by
          rw [space,size,plane]; ring
        _ ≤ 3*N*B^(j+1)+(N*r)*B^(j+1) := Nat.add_le_add parent child
        _ = (3+r)*(N*B^(j+1)) := by ring
        _ ≤ B*(N*B^(j+1)) := larger
        _ = N*B^((j+1)+1) := by rw [pow_succ]; ring
  refine ⟨B*(b^B),B,?_⟩
  intro n hn
  have h := batch (depth b n) 1
  simp only [Nat.one_mul] at h
  calc
    _ ≤ B^(depth b n+1) := h
    _ = B*B^(depth b n) := by rw [pow_succ,Nat.mul_comm]
    _ ≤ B*((b*n)^B) := Nat.mul_le_mul_left B (depth_poly hb hn B)
    _ = (B*b^B)*n^B := by rw [mul_pow,Nat.mul_assoc]

end VWZClique.BlockMM.WordLayout
end

/- NativeSquareChoice -/
section
namespace VWZClique.IntegerRAM.Projected.SquareCaller
open SquareCode.Layout BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

/-- Choose the same native matrix scheme simultaneously for all projected
tiles, with numeric bounds for its call duration and its scratch address space. -/
theorem choose (η : ℝ) (hη : 0<η) :
    ∃ (b r : ℕ) (_ : 2 ≤ b) (S : Scheme b r) (C : ℝ) (U d : ℕ), 0<S.scale ∧ 0<r ∧ 0<C ∧
      ∀ n : ℕ, 1 ≤ n → ((duration S n:ℕ):ℝ) ≤ C*(n:ℝ)^(omega ℂ+η) ∧
        space b r (depth b n) 1 ≤ U*n^d := by
  obtain ⟨b,r,hb,S,hs,_,K,hK,cost⟩ := integer_uniform_at_omega η hη
  have hr := rank_pos S (by omega) hs
  obtain ⟨P,Q,rate⟩ := runtime_le S hb hr
  obtain ⟨U,d,spaceBound⟩ := polynomial_space (r:=r) hb
  refine ⟨b,r,hb,S,(P:ℝ)*K+Q+1,U,d,hs,hr,by positivity,?_⟩
  intro n hn
  refine ⟨?_,spaceBound n hn⟩
  have bound : duration S n ≤ P*scalarBudget b r (depth b n)+Q*(n*n) :=
    rate ⟨n,b^(depth b n),0,0,0,0⟩ hn rfl
  have cast : (duration S n:ℝ) ≤ (P:ℝ)*(scalarBudget b r (depth b n):ℝ)+(Q:ℝ)*((n:ℝ)*n) := by exact_mod_cast bound
  have mul := mul_le_mul_of_nonneg_left (cost n hn) (Nat.cast_nonneg P)
  have two := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤n)
    (show (2:ℝ) ≤ omega ℂ+η by linarith [MM.omega_two_le ℂ])
  rw [Real.rpow_two] at two
  have q := mul_le_mul_of_nonneg_left two (Nat.cast_nonneg Q)
  have pos : 0 ≤ (n:ℝ)^(omega ℂ+η) := by positivity
  nlinarith only [cast,mul,q,pos]

end VWZClique.IntegerRAM.Projected.SquareCaller
end

/- NativeProjectLargeBounds -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode.Layout BlockMM BlockMM.WordLayout UniformFolds TraceDyadic Double IntegerTiling

theorem pointers_of_params {base n cnt : ℕ} {m : IntegerRAM.Memory} (p : Init.Params base n cnt m) :
    Pointers m (workspaceBanks (MaskScan.Arena.slot base n 7+2) n) :=
  ⟨p.source,p.middle,p.right,p.raw,p.wt,p.leftPack,p.rightPack,p.product⟩

/-- One polynomial address bound covers tile scheduling, table layout and
the complete workspace of the square-multiplication program. -/
theorem limits_of_workspace {base rank q L start M U d : ℕ} (labels : Finset (BasisLabel L))
    (spaceRate : ∀ s : ℕ, 1 ≤ s → space base rank (depth base s) 1 ≤ U*s^d)
    (header : 378 ≤ start) (ratio : 2*2^L*q ≤ M) (maximum : start+12*(2^L)^6+U*(2^L)^(3*d) ≤ M) :
    let e := effectiveTile q L labels.card
    let s := IntegerTiling.side L e
    let p := blocks L e
    Limits base rank q L labels.card s p (workspaceBanks start (2^L)) M := by
  dsimp only
  let n := (2:ℕ)^L
  let e := effectiveTile q L labels.card
  let s := IntegerTiling.side L e
  let p := blocks L e
  let l := workspaceBanks start n
  have hN : 1 ≤ n := by change 0<(2:ℕ)^L; positivity
  have width : 0<s := by dsimp [s,IntegerTiling.side]; positivity
  have pk : 0<p := by dsimp [p,blocks]; positivity
  have hs := projectionShape_all q labels
  have mulN : p*s=n^3 := hs.2
  have one : s ≤ n^3 := (by simpa using (Nat.mul_le_mul_right s pk) : s ≤ p*s).trans_eq mulN
  have ha : labels.card ≤ n^2 := by
    have c : labels.card ≤ (4:ℕ)^L := by simpa [BasisLabel] using Finset.card_le_univ labels
    exact c.trans_eq (by dsimp [n]; rw [show (4:ℕ)=(2:ℕ)^2 by decide,←pow_mul,←pow_mul,Nat.mul_comm 2 L])
  obtain ⟨w,mid,_,tile,pack⟩ := Workspace.table_sizes ha one mulN
  have ds : 1 ≤ n^6 := Nat.one_le_pow _ _ hN
  have sg : l.bound s (labels.card*n) p := by
    dsimp [l,workspaceBanks,Workspace.banks,Banks.bound] at *
    rw [mulN,Nat.mul_comm (n^3) (labels.card*n)]
    omega
  have sPow := Nat.pow_le_pow_left one d
  have add := Nat.mul_le_mul_left U sPow
  rw [←pow_mul] at add
  have work := Workspace.end_bound start n hN
  have fit := spaceRate s width
  have bM : l.output+s*s+space base rank (depth base s) 1 ≤ M := by
    change (Workspace.banks start n).output+s*s+space base rank (depth base s) 1 ≤ M
    change start+12*n^6+U*n^(3*d) ≤ M at maximum
    omega
  have n3 : n^3 ≤ n^6 := Nat.pow_le_pow_right hN (by decide)
  have nmax : labels.card*n ≤ n^3 := by simpa [pow_succ] using Nat.mul_le_mul_right n ha
  have Ln : L<n := Nat.lt_two_pow_self
  have nle : n ≤ n^6 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 6)
  change start+12*n^6+U*n^(3*d) ≤ M at maximum
  refine ⟨by simpa [pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using ratio,by change n^3+1 ≤ M; omega,
    by change labels.card*n ≤ M; omega,by omega,bM,sg,?_,?_⟩
  · dsimp [workspaceBanks,Workspace.banks]; change 378<start+4*n^3+3*n^6; omega
  · dsimp [workspaceBanks,Workspace.banks]; change start+4*n^3+3*n^6<start+4*n^3+4*n^6; omega

end VWZClique.IntegerRAM.Projected.Large
end

/- NativeProjectionCapacity -/
section
namespace VWZClique.IntegerRAM.Projected.Capacity
open UniformFolds BlockMM BlockMM.WordLayout

abbrev startAt (base n : ℕ) := MaskScan.Arena.slot base n 7+2
abbrev layout (base n : ℕ) := Workspace.banks (startAt base n) n

/-- All address and integer word requirements for one projected trace.
They use the caller's fixed scheme and fixed edge-count parameters. -/
structure Bounds (b c U d K q base L M : ℕ) : Prop where
  supportRoom : startAt base (2^L)+3*8^L ≤ M
  windowRatio : 2^(L+1)*(4*K) ≤ M
  padding : b*2^L+1 ≤ M
  tileRatio : 2*2^L*q ≤ M
  maximum : startAt base (2^L)+12*(2^L)^6+U*(2^L)^(3*d) ≤ M
  normalize : normalizeRoom c L ≤ M
  countAddr : Projected.countAddr base (2^L) ≤ M
  small : (layout base (2^L)).weights+4*(2^L*2^L)+U*(2^L)^d ≤ M
  dense : (layout base (2^L)).output+(2^L)^6 ≤ M
  counter : ∀ a ≤ (2^L)^2, a*2^L*2^L ≤ M

def coefficient (b c U K q : ℕ) := 140+b+8*K+2*q+U+2^(3+4*c)
def power (c d : ℕ) := max (max 6 (3*d)) (23+6*c)

theorem make {b c U d K q base L M : ℕ}
    (room : base+coefficient b c U K q*(2^L)^power c d ≤ M) : Bounds b c U d K q base L M := by
  let n := 2^L
  let p := power c d
  let s := startAt base n
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have hp : 6 ≤ p := (le_max_left ..).trans (le_max_left ..)
  have hwd : 3*d ≤ p := (le_max_right ..).trans (le_max_left ..)
  have hnorm : 23+6*c ≤ p := le_max_right ..
  have nd : n^d ≤ n^(3*d) := Nat.pow_le_pow_right hn (by omega)
  have np (i : ℕ) (hi : i ≤ p) : n^i ≤ n^p := Nat.pow_le_pow_right hn hi
  have one : 1 ≤ n^p := Nat.one_le_pow _ _ hn
  have n1 : n ≤ n^p := by simpa using np 1 (by omega)
  have n2 := np 2 (by omega)
  have n3 := np 3 (by omega)
  have n6 := np 6 hp
  have n4 := np 4 (by omega)
  have fit : base+(140+b+8*K+2*q+U+2^(3+4*c))*n^p ≤ M := room
  simp only [Nat.add_mul] at fit
  have size : s=base+9*n+81*(n*n)+7*n^3+2 := by
    simp [s,startAt,MaskScan.Arena.slot,MaskScan.Arena.origin,MaskScan.Arena.span,pow_two]
  have high : s ≤ base+99*n^p := by rw [size,←pow_two];omega
  have eight : (8:ℕ)^L=n^3 := by dsimp [n];rw [←pow_mul,Nat.mul_comm,pow_mul];rfl
  have r1 := Nat.mul_le_mul_left (8*K) n1
  have r2 := Nat.mul_le_mul_left (2*q) n1
  have pad := Nat.mul_le_mul_left b n1
  have ws := Nat.mul_le_mul_left U (np (3*d) hwd)
  have norm := Nat.mul_le_mul_left (2^(3+4*c)) (np (23+6*c) hnorm)
  have maxB : s+12*n^6+U*n^(3*d) ≤ M := by omega
  have sm := Nat.mul_le_mul_left U nd
  have smallRange : (layout base n).weights+4*(n*n)+U*n^d ≤ M := by
    change s+4*n^3+4*n^6+4*(n*n)+U*n^d ≤ M
    rw [←pow_two];omega
  have cnt : Projected.countAddr base n+2=s := by simp [Projected.countAddr,size]
  refine ⟨?_,?_,?_,?_,maxB,?_,by change Projected.countAddr base n ≤ M;omega,smallRange,?_,?_⟩
  · change s+3*8^L ≤ M;rw [eight];omega
  · rw [pow_succ];change n*2*(4*K) ≤ M
    rw [show n*2*(4*K)=(8*K)*n by ring];omega
  · change b*n+1 ≤ M;omega
  · change 2*n*q ≤ M;rw [show 2*n*q=(2*q)*n by ring];omega
  · rw [normalizeRoom_polynomial];change 2^(3+4*c)*n^(23+6*c) ≤ M;omega
  · have lim := Workspace.end_bound s n hn
    change (Workspace.banks s n).output+n^6 ≤ M;omega
  · intro a ha
    change a ≤ n^2 at ha
    have sz := Nat.mul_le_mul_right (n*n) ha
    rw [show n^2*(n*n)=n^4 by ring,←Nat.mul_assoc] at sz
    change a*n*n ≤ M;omega

theorem Bounds.smallSpace {b r c U d K q base L M : ℕ} (h : Bounds b c U d K q base L M)
    (spaceRate : ∀ s : ℕ, 1 ≤ s → space b r (depth b s) 1 ≤ U*s^d) :
    (layout base (2^L)).weights+4*(2^L*2^L)+space b r (depth b (2^L)) 1 ≤ M := by
  exact (Nat.add_le_add_left (spaceRate _ (Nat.one_le_pow _ _ (by decide))) _).trans h.small

noncomputable def graphCoefficient (b c U : ℕ) :=
  Finset.univ.sup (fun i : Fin 37 => coefficient b c U (windowAt i.val) (tileAt i.val))

theorem forGraph {b c U d base L M : ℕ} (H : SimpleGraph V)
    (fit : base+graphCoefficient b c U*(2^L)^power c d ≤ M) :
    Bounds b c U d (windowAt (Nat.card H.edgeSet)) (tileAt (Nat.card H.edgeSet)) base L M := by
  let i : Fin 37 := ⟨Nat.card H.edgeSet,by have := edge_limit H;omega⟩
  have co : coefficient b c U (windowAt i.val) (tileAt i.val) ≤ graphCoefficient b c U :=
    Finset.le_sup (f:=fun j : Fin 37 => coefficient b c U (windowAt j.val) (tileAt j.val)) (Finset.mem_univ i)
  exact make ((Nat.add_le_add_left (Nat.mul_le_mul_right _ co) _).trans fit)

end VWZClique.IntegerRAM.Projected.Capacity
end

/- NativeProjectionTail -/
section
namespace VWZClique.IntegerRAM.Projected.Tail
open Structured UniformFolds NativeTraversal NativeFrame NativeArena BlockMM BlockMM.WordLayout Double

noncomputable def command {b r : ℕ} (S : Scheme b r) (q d : ℕ) : Command :=
  .seq (Large.code q S) (.seq (combineScales 367 SquareCode.Layout.scaleReg) (finalize d))

theorem run {W M L root output d b r U p : ℕ} (S : Scheme b r)
    (hb : 2 ≤ b) (hr : 0 < r) (hc : 0 < S.scale) (large : 512 ≤ root) (hd : d ≤ 36)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ) (bin : ∀ i, Binary (w i))
    (stack : List (NativeTraversal.Slot L)) {orig m : Memory}
    (src : Repr (NativeArena.layout L root output large) (.input d w::stack) orig)
    (space : ∀ x : ℕ, 1 ≤ x → BlockMM.WordLayout.space b r (depth b x) 1 ≤ U*x^p)
    (room : Graph.Division.Room W M) :
    let N := 2^L
    let base := atDepth root N d
    let start := Capacity.startAt base N
    let K := windowAt (Nat.card H.edgeSet)
    let q := tileAt (Nat.card H.edgeSet)
    let labels := (qOf H L).labels
    let t := effectiveTile q L labels.card
    let s := IntegerTiling.side L t
    let banks := Large.workspaceBanks start N
    let cw := (Round.mk H π (none : Option (Mask L)) none).inputs w
    let c := S.scale.toNat
    let P := (c^depth b N:ℕ)
    Capacity.Bounds b c U p K q base L M →
    Preparation.Ready L K base labels.card b c w m →
    (∀ j : ℕ, projectionPrefix base N j → m j=orig j) →
    Large.Sources m banks (scaleMat (P:ℤ) (shortWeight labels K cw))
      (scaleMat (P:ℤ) (middle labels t cw)) (scaleMat (P:ℤ) (Projected.right labels t cw)) →
    ∃ f ≤ Large.cost q S L s (IntegerTiling.blocks L t)+3+(13*(21*L+3)+44), ∃ o,
      Runs W (command S q d) m f o ∧ Repr (NativeArena.layout L root output large)
        (.cursor d H π .left w 0 (integerTrace K L H π w)::stack) o := by
  intro N base start K q labels t s banks cw c P cap ready prior sources
  have baseLo : 512 ≤ base := (NativeArena.layout L root output large).large d
  have startLo : base ≤ start := by dsimp [start,Capacity.startAt,MaskScan.Arena.slot,MaskScan.Arena.origin]; omega
  have before : start < banks.temp := by
    dsimp [banks,Large.workspaceBanks,Workspace.banks]; have hp : 0 < N^3 := by dsimp [N]; positivity
    omega
  have lim := Large.limits_of_workspace (q:=q) labels space (by omega : 378 ≤ start) cap.tileRatio cap.maximum
  obtain ⟨u,hu,x,rx,num,scale,fr⟩ := Large.from_dense S hb hr labels cw (P:ℤ) K banks m
    (Large.pointers_of_params ready.params) room ready.domain ready.length ready.params.size lim sources
  obtain ⟨y,ry,sc,keep⟩ := combineScales_runs (W:=W) 367 SquareCode.Layout.scaleReg (by decide) (by decide) x
  have pres (j : ℕ) (hj : j < banks.temp) : y j=m j :=
    (keep j (by dsimp [scaleReg]; omega)).trans (fr j hj)
  have oldscale : x 367=(P:ℤ) := (fr 367 (by omega)).trans ready.scale
  have castc : (c:ℤ)=S.scale := Int.toNat_of_nonneg hc.le
  have eq : (commonScale c b L s:ℤ)=(P:ℤ)^3*S.scale^(depth b s) := by
    simp only [commonScale,P,N,Nat.cast_mul,Nat.cast_pow,castc]
  have prepared : MaskScan.Arena.Prepared L K base y := by
    apply ready.metadata.congr
    intro j lo hi
    apply pres
    change j < start at hi
    omega
  have pref (j : ℕ) (h : projectionPrefix base N j) : y j=orig j := by
    apply (pres j ?_).trans (prior j h)
    rcases h with h|h|h|⟨lo,hi⟩ <;> try omega
    have hmeta : metaBase base N ≤ start := by
      dsimp [start,Capacity.startAt,MaskScan.Arena.slot,MaskScan.Arena.origin,metaBase,tableWords]; rw [pow_two];omega
    omega
  have small : s ≤ N^3 := by
    have pos : 1 ≤ IntegerTiling.blocks L t := Nat.one_le_pow _ _ (by decide)
    exact (Nat.le_mul_of_pos_left _ pos).trans_eq (IntegerTiling.exact_shape L t)
  obtain ⟨v,o,hv,rv,done⟩ := finalize_in_arena (b:=b) (c:=c) large (by exact Int.pos_iff_toNat_pos.mp hc) hb small hd H π w bin stack src prepared pref
    (lt_of_le_of_lt (by exact_mod_cast cap.normalize) room) room cap.countAddr
    (by rw [eq]; exact (keep rawTrace (by decide)).trans num) (by rw [eq,sc,oldscale,scale])
  change u≤Large.cost q S L s (IntegerTiling.blocks L t) at hu
  exact ⟨u+(3+v),by omega,o,.seq rx (.seq ry rv),done⟩
end VWZClique.IntegerRAM.Projected.Tail
end

/- NativeProjectionLeftJob -/
section
namespace VWZClique.IntegerRAM.Projected.LeftSetup
open Structured FoldBits Butterfly UniformFolds TraceDyadic Double

theorem budget_le {a L : ℕ} (small : a≤(2^L)^2) : budget L a≤256*((L+1)*(2^L)^2) := by
  let n := (2^L)^2
  let total := (L+1)*n
  have large : 0<n := by dsimp [n];positivity
  have al : a≤total := small.trans (Nat.le_mul_of_pos_left _ (by omega))
  have len : L+1≤total := Nat.le_mul_of_pos_right _ large
  have eq : 4^L=n := by change 4^L=(2^L)^2;rw [←pow_mul,Nat.mul_comm,pow_mul];rfl
  have bt : 5+L*(15+20*4^(L-1))≤57*total := by
    have h := Butterfly.dense_budget L
    rw [eq,Nat.mul_assoc] at h
    exact le_trans (by omega) h
  change budget L a≤256*total
  simp only [budget,LeftGather.address,LeftGather.val,LeftGather.source,LeftGather.entry,SquareCode.Expr.steps]
  omega

end VWZClique.IntegerRAM.Projected.LeftSetup
end

/- NativeProjectionScatterHeader -/
section
namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured UniformFolds FoldBits

theorem header_cost (L : ℕ) : 16+24*L+128*(2^L)^2≤168*(2^L)^2 := by
  have hx := Nat.lt_two_pow_self (n:=L)
  have h : 0<2^L := by positivity
  nlinarith [Nat.mul_le_mul_right (2^L) (show 1≤2^L from h)]

end VWZClique.IntegerRAM.Projected.Scatter
end

/- NativeProjectionPipeline -/
section
namespace VWZClique.IntegerRAM.Projected.Pipeline
open Structured NativeFrame UniformFolds NativeTraversal NativeArena BlockMM Double WeightedProof

noncomputable def code {b r : ℕ} (S : Scheme b r) (d : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) : Command :=
  let e := Nat.card H.edgeSet
  .seq (Preparation.command d (windowAt e) b S.scale.toNat)
    (.seq (Dense.code S π (slots π H)) (Tail.command S (tileAt e) d))

noncomputable def fuel {b r : ℕ} (S : Scheme b r) (d L : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V) :=
  let e := Nat.card H.edgeSet
  let a := (qOf H L).labels.card
  let q := tileAt e
  let t := effectiveTile q L a
  Preparation.ticks d (windowAt e) b S.scale.toNat L + (Dense.cost S π (slots π H) L a +
    (Large.cost q S L (IntegerTiling.side L t) (IntegerTiling.blocks L t)+3+(13*(21*L+3)+44)))

theorem execute {W L root out d b r U p : ℕ} (S : Scheme b r)
    (hb : 2 ≤ b) (hr : 0 < r) (hc : 0 < S.scale)
    (space : ∀ x : ℕ, 1 ≤ x → WordLayout.space b r (depth b x) 1 ≤ U*x^p)
    (large : 512 ≤ root) (hL : 0 < L) (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (stack : List (NativeTraversal.Slot L)) (hd : d ≤ 36) (bin : ∀ i, Binary (w i))
    (room : Graph.Division.Room W (atDepth root (2^L) d+Capacity.graphCoefficient b S.scale.toNat U*(2^L)^Capacity.power S.scale.toNat p)) :
    Transition W (Repr (NativeArena.layout L root out large)) (code S d H π)
      (.input d w::stack) (.cursor d H π .left w 0 (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::stack)
      (fuel S d L H π) := by
  intro m src
  let base := atDepth root (2^L) d
  let M := base+Capacity.graphCoefficient b S.scale.toNat U*(2^L)^Capacity.power S.scale.toNat p
  have bounds := Capacity.forGraph (b:=b) (c:=S.scale.toNat) (U:=U) (d:=p) (base:=base) (L:=L) (M:=M) H le_rfl
  let K := windowAt (Nat.card H.edgeSet)
  let q := tileAt (Nat.card H.edgeSet)
  let a := (qOf H L).labels.card
  let t := effectiveTile q L a
  let round := Round.mk H π (none : Option (Mask L)) none
  have hw := round.inputs_property w Binary (Or.inr rfl) bin
  obtain ⟨f,hf,x,rx,ready,fr⟩ := Preparation.run (c:=S.scale.toNat) large hd hb H w stack m room bounds.supportRoom bounds.windowRatio bounds.padding src
  obtain ⟨g,hg,y,ry,readyY,banks,fy⟩ := Dense.all_runs S hb hr π (slots π H) t w hw x hL
    ((NativeArena.layout L root out large).large d) ready room (bounds.smallSpace space)
  have conv : ((S.scale.toNat ^ depth b (2^L) : ℕ):ℤ)= S.scale^depth b (2^L) := by rw [Nat.cast_pow,Int.toNat_of_nonneg hc.le]
  obtain ⟨h,hh,z,rz,done⟩ := Tail.run S hb hr hc large hd H π w bin stack src space room bounds readyY
    (fun j hj => (fy j hj).trans (fr j hj)) (by rw [conv];exact banks)
  exact ⟨_,Nat.add_le_add hf (Nat.add_le_add hg hh),z,.seq rx (.seq ry rz),done⟩

end VWZClique.IntegerRAM.Projected.Pipeline
end

/- NativeProjectionChannelCost -/
section
namespace VWZClique.IntegerRAM.Projected.Channels
open BlockMM Projection Scatter

private theorem sheet_le (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3)
    (g : Group) {n : ℕ} (hn : 1 ≤ n) :
    Small.sheetTime π E rev h g n ≤ Small.sheetTime π E rev h g 1*n^2 := by
  have h1 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn
  have h2 : n ≤ n^2 := by simpa using Nat.pow_le_pow_right hn (by decide : 1 ≤ 2)
  have ar (H A : ℕ) : H+(2+n*(1+n*A+3)) ≤ (H+(2+1*(1+1*A+3)))*n^2 := by
    have h0 := Nat.mul_le_mul_left (H+2) h1
    have h4 := Nat.mul_le_mul_left 4 h2
    nlinarith only [h0,h4]
  exact ar _ _

private theorem job_le (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3)
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    Small.jobTime π E rev h n K ≤ K+Small.jobTime π E rev h 1 0*n^2 := by
  have h1 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn
  have ar {x y z X Y Z : ℕ} (d e : ℕ) (hx : x ≤ X*n^2) (hy : y ≤ Y*n^2) (hz : z ≤ Z*n^2) :
      x+(y+(z+(d+(K+(e+9*(n*n)))))) ≤ K+(X+(Y+(Z+(d+(0+(e+9*(1*1)))))))*n^2 := by
    have hd := Nat.mul_le_mul_left d h1
    have he := Nat.mul_le_mul_left e h1
    nlinarith only [hx,hy,hz,hd,he]
  apply ar _ _ <;> apply sheet_le _ _ _ _ _ hn

private abbrev Patterns := Equiv.Perm V × Finset EdgeSlot × Bool × Fin 3

private noncomputable def patternTime (p : Patterns) : ℕ :=
  Small.jobTime p.1 p.2.1 p.2.2.1 p.2.2.2 1 0

private noncomputable def fixed : ℕ := (Finite.exists_le patternTime).choose

private theorem pattern_le (p : Patterns) : patternTime p ≤ fixed :=
  (Finite.exists_le patternTime).choose_spec p

private theorem arithmetic {U V D T F n a : ℕ} (small : U ≤ D+V*n^2) (bound : V ≤ F)
    (scatter : T ≤ 168*n^2) (hn : 1 ≤ n^2) :
    9+(a*n*n)*((U+T)+17) ≤ (F+194)*(1+a*n^2*D+a*n^4) := by
  have u := Nat.mul_le_mul_right (n^2) bound
  have tidy : U+T+17 ≤ D+(F+185)*n^2 := by nlinarith only [small,u,scatter,hn]
  apply (Nat.add_le_add_left (Nat.mul_le_mul_left (a*n*n) tidy) 9).trans
  ring_nf
  omega

/-- A single instruction constant for all finite graph patterns, relabelings
and three choices of channel. -/
noncomputable def constant : ℕ := fixed+194

theorem cost_quadratic {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (ch : Channel) (L a : ℕ) :
    let n := 2^L
    cost S π E ch L a ≤ constant*(1+a*n^2*SquareCaller.duration S n+a*n^4) := by
  intro n
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have h1 : 1 ≤ n^2 := Nat.one_le_pow _ _ hn
  exact arithmetic (job_le π E (rev ch) (index ch) hn (SquareCaller.duration S n))
    (pattern_le (π,E,rev ch,index ch)) (Scatter.header_cost L) h1

end VWZClique.IntegerRAM.Projected.Channels
end

/- NativeProjectionLeftGridCost -/
section
namespace VWZClique.IntegerRAM.Projected.LeftSetup

theorem grid_time {a L : ℕ} (ha : a≤(2^L)^2) :
    9+(a*2^L*2^L)*(budget L a+17) ≤ 9+273*a*(L+1)*(2^L)^4 := by
  let n := 2^L
  have hn : 0<n^2 := by dsimp [n]; positivity
  have positive : 0<(L+1)*n^2 := Nat.mul_pos (by omega) hn
  have body : budget L a+17≤273*((L+1)*n^2) := by have := budget_le ha;change budget L a≤256*((L+1)*n^2) at this;omega
  have grid := Nat.mul_le_mul_left (a*n*n) body
  change 9+(a*n*n)*(budget L a+17)≤9+273*a*(L+1)*n^4
  calc
    _ ≤ 9+(a*n*n)*(273*((L+1)*n^2)) := Nat.add_le_add_left grid _
    _ = _ := by ring

end VWZClique.IntegerRAM.Projected.LeftSetup
end

/- NativeProjectAccounting -/
section
namespace VWZClique.IntegerRAM.Projected.Accounting
open SquareCode SquareCode.Layout BlockMM BlockMM.WordLayout UniformFolds Double

theorem square_le_duration {b r : ℕ} (S : Scheme b r) (s : ℕ) :
    s*s ≤ SquareCaller.duration S s := by
  let a : Anchors := ⟨s,b^(depth b s),0,0,0,0⟩
  have fit : s*s ≤ gridCost 1 s (tileSteps true) := by
    dsimp [gridCost]; nlinarith
  have copy : s*s ≤ (copyInto .left 0).cost a := by
    apply fit.trans
    exact Nat.le_add_left _ _
  dsimp only [SquareCaller.duration,runtimeCost]
  dsimp only [a] at copy
  omega

/-- Counts of the operations performed by the three small slice families,
the retained-label transform, the tile preparations and the large products. -/
def components (mm : ℕ → ℕ) (q L a : ℕ) :=
  let n := 2^L
  let t := effectiveTile q L a
  let s := IntegerTiling.side L t
  let k := IntegerTiling.blocks L t
  n^5 + 3*(a*n^2*mm n) + a*n^4 + k*mm s + k*(s*s) + (a*n)*(a*n) + 1

theorem components_le {mm : ℕ → ℕ} (sq : ∀ s, s*s ≤ mm s) (q L a T : ℕ) :
    components mm q L a ≤ 2*((projectionWork mm T q L a + (2^L)^5)+1) := by
  let n := 2^L
  let e := effectiveTile q L a
  let s := IntegerTiling.side L e
  let k := IntegerTiling.blocks L e
  let v := (a*n)*(a*n)
  have tile := Nat.mul_le_mul_left k (sq s)
  have eq : projectionWork mm T q L a =
    3*(a*n^2*mm n) + 387*(a*n^4) + a*n^2*(T*(L+1)*4^L) + v +
      k*mm s + k*v + 2*v := by
    dsimp only [projectionWork,Double.budget,n,e,s,k,v]
    ring
  rw [eq]
  change n^5 + 3*(a*n^2*mm n) + a*n^4 + k*mm s + k*(s*s) + v + 1 ≤ _
  dsimp only [n] at *
  omega

theorem unified {b r : ℕ} (S : Scheme b r) (T L K : ℕ) (H : SimpleGraph V) :
    K*components (SquareCaller.duration S) (tileAt (Nat.card H.edgeSet)) L (NativeTraversal.qOf H L).labels.card ≤
      (2*K)*(NativeTraversal.projected (SquareCaller.duration S) T 1 L H+1) := by
  have h := Nat.mul_le_mul_left K (components_le (square_le_duration S) (tileAt (Nat.card H.edgeSet)) L (NativeTraversal.qOf H L).labels.card T)
  simpa [NativeTraversal.projected,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

end VWZClique.IntegerRAM.Projected.Accounting
end

/- NativeProjectionCostArithmetic -/
section
namespace VWZClique.IntegerRAM.Projected.Accounting

/-- Combine three grids of native square slices with the final
butterfly-and-gather grid, including its empty-table initialization. -/
theorem dense_grid_bound (mm : ℕ → ℕ) (q L a C t₁ t₂ t₃ t₄ : ℕ)
    (h₁ : t₁ ≤ C*(1+a*(2^L)^2*mm (2^L)+a*(2^L)^4))
    (h₂ : t₂ ≤ C*(1+a*(2^L)^2*mm (2^L)+a*(2^L)^4))
    (h₃ : t₃ ≤ C*(1+a*(2^L)^2*mm (2^L)+a*(2^L)^4))
    (h₄ : t₄ ≤ 9+273*a*(L+1)*(2^L)^4) :
    t₁+(t₂+t₃)+t₄ ≤ (3*C+282)*(L+1)*components mm q L a := by
  let n := 2^L
  let D := components mm q L a
  let B := 1+a*n^2*mm n+a*n^4
  have hB : B ≤ D := by unfold B D components;dsimp only;change _ ≤ n^5+3*(a*n^2*mm n)+a*n^4+_+_+_+1;omega
  have F : a*n^4 ≤ D := by dsimp [B] at hB;omega
  have pos : 1 ≤ D := by dsimp [B] at hB;omega
  have l : 1 ≤ L+1 := by omega
  have H := Nat.mul_le_mul_left C hB
  have X : D ≤ (L+1)*D := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right D l
  have Y := Nat.mul_le_mul_left C X
  have Z := Nat.mul_le_mul_left (L+1) F
  have Z' := Nat.mul_le_mul_left 273 Z
  change t₁ ≤ C*B at h₁
  change t₂ ≤ C*B at h₂
  change t₃ ≤ C*B at h₃
  change t₄ ≤ 9+273*a*(L+1)*n^4 at h₄
  rw [show 273*a*(L+1)*n^4=273*((L+1)*(a*n^4)) by ring] at h₄
  change _ ≤ (3*C+282)*(L+1)*D
  rw [Nat.mul_assoc,Nat.add_mul,Nat.mul_assoc 3]
  omega

end VWZClique.IntegerRAM.Projected.Accounting
end

/- NativeProjectionDenseCost -/
section
namespace VWZClique.IntegerRAM.Projected.Dense
open BlockMM Projection

noncomputable def costCoefficient := 3*Channels.constant+282

theorem cost_bound {b r : ℕ} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (q L a : ℕ) (ha : a ≤ (2^L)^2) :
    cost S π E L a ≤ costCoefficient*(L+1)*Accounting.components (SquareCaller.duration S) q L a := by
  unfold cost threeCost costCoefficient
  exact Accounting.dense_grid_bound (SquareCaller.duration S) q L a Channels.constant
    (Channels.cost S π E .middle L a) (Channels.cost S π E .right L a)
    (Channels.cost S π E .left L a) (9+a*2^L*2^L*(LeftSetup.budget L a+17))
    (Channels.cost_quadratic S π E .middle L a) (Channels.cost_quadratic S π E .right L a)
    (Channels.cost_quadratic S π E .left L a) (LeftSetup.grid_time ha)

end VWZClique.IntegerRAM.Projected.Dense
end

/- NativeProjectLargeRate -/
section
namespace VWZClique.IntegerRAM.Projected.Large
open SquareCode.Layout BlockMM Packing

private theorem tile_bound (role : Role) {s : ℕ} (hs : 1 ≤ s) :
    planeCost role s ≤ (cellCost role+9)*(s*s) := by
  have a : s ≤ s*s := by simpa using Nat.mul_le_mul_left s hs
  have b : 1 ≤ s*s := hs.trans a
  unfold planeCost
  ring_nf at a b ⊢
  omega

private theorem packet_bound (role : Role) (i o : ℕ) {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    bankCost role i o n s ≤ (setupCost (select i o)+cellCost role+16)*(n*(s*s)) := by
  let X := n*(s*s)
  have sq : 1 ≤ s*s := Nat.mul_pos hs hs
  have nX : n ≤ X := by simpa [X] using Nat.mul_le_mul_left n sq
  have oneX : 1 ≤ X := hn.trans nX
  have c := tile_bound role hs
  have byN := Nat.mul_le_mul_left n c
  have st := Nat.mul_le_mul_left (setupCost (select i o)) oneX
  simp only [Nat.mul_one] at st
  change setupCost (select i o)+(3+n*(planeCost role s+4)) ≤ _
  have term : n*((cellCost role+9)*(s*s))=(cellCost role+9)*X := by dsimp [X]; ring
  rw [term] at byN
  change _ ≤ (setupCost (select i o)+cellCost role+16)*X
  (try ring_nf at byN); (try ring_nf at st); (try ring_nf at nX); (try ring_nf at oneX); ring_nf
  omega

private theorem packs_bound : ∃ D : ℕ, ∀ s n : ℕ, 1 ≤ s → 1 ≤ n → allCost s n ≤ D*(n*(s*s)) := by
  let A := setupCost (select 371 375)+cellCost .weight+9
  let B := setupCost (select 372 376)+cellCost .middle+16
  let C := setupCost (select 373 377)+cellCost .right+16
  refine ⟨A+B+C,?_⟩
  intro s n hs hn
  have nSq : s*s ≤ n*(s*s) := by simpa using Nat.mul_le_mul_right (s*s) hn
  have h1 := Nat.mul_pos hs hs
  have f := Nat.mul_le_mul_left (setupCost (select 371 375)) h1
  simp only [Nat.mul_one] at f
  have tile : setupCost (select 371 375)+planeCost .weight s ≤ A*(n*(s*s)) := by
    apply (show _ ≤ A*(s*s) from ?_).trans (Nat.mul_le_mul_left A nSq)
    have sums := Nat.add_le_add f (tile_bound .weight hs)
    exact sums.trans_eq (by dsimp [A]; ring)
  have total := Nat.add_le_add tile (Nat.add_le_add (packet_bound .middle 372 376 hn hs) (packet_bound .right 373 377 hn hs))
  exact total.trans_eq (by dsimp only [B,C]; ring)

private theorem shape_bound (q : ℕ) : ∃ K : ℕ, ∀ L : ℕ, Projected.Shape.amount q L ≤ K*(L+1) := by
  let A := setupCost Projected.Shape.header+q+17+setupCost Projected.Shape.exponents+10+
    setupCost Projected.Shape.chooseGap+1+setupCost Projected.Shape.fallback
  refine ⟨A+29,?_⟩
  intro L
  have hA : A ≤ A*(L+1) := by simpa using Nat.mul_le_mul_left A (show 1 ≤ L+1 by omega)
  have eq : Projected.Shape.amount q L=A+13*(L+1)+16*L := by unfold Projected.Shape.amount; dsimp [A]; omega
  rw [eq,Nat.add_mul]; omega

/-- The input-dependent work beyond the native matrix calls is one constant
per packed entry plus O(L) for the tile selection. -/
theorem cost_bound {b r : ℕ} (hb : 2 ≤ b) (q : ℕ) (S : Scheme b r) :
    ∃ D : ℕ, ∀ L s n : ℕ, 1 ≤ s → 1 ≤ n →
      cost q S L s n ≤ D*((L+1)+n*(s*s)) + n*SquareCaller.duration S s := by
  obtain ⟨A,aBudget⟩ := packs_bound
  obtain ⟨B,bBudget⟩ := shape_bound q
  let J := setupCost setSide+2+1+setupCost controls+1
  let C := A+B+J+padSteps b S.scale*b+24
  refine ⟨C,?_⟩
  intro L s n hs hn
  let X := n*(s*s)
  have h1 := Nat.mul_pos hs hs
  have nX : n ≤ X := by simpa [X] using Nat.mul_le_mul_left n h1
  have sSq : s ≤ s*s := by simpa using Nat.mul_le_mul_left s hs
  have sqX : s*s ≤ X := by simpa [X] using Nat.mul_le_mul_right (s*s) hn
  have hh (h : ℕ) : h ≤ b^h := by
    induction h with
    | zero => simp
    | succ h ih => have := Nat.pow_pos (by omega : 0<b) (n:=h); rw [pow_succ]; nlinarith
  have dep := (hh _).trans (depth_bounds hb hs).2
  have ds := Nat.mul_le_mul_left (padSteps b S.scale) (dep.trans (Nat.mul_le_mul_left b (sSq.trans sqX)))
  have per : depth b s*padSteps b S.scale ≤ (padSteps b S.scale*b)*X := by
    simpa only [Nat.mul_assoc,Nat.mul_comm (depth b s)] using ds
  have jf : J ≤ J*X := by simpa using Nat.mul_le_mul_left J (hn.trans nX)
  have tot := aBudget s n hs hn
  change allCost s n ≤ A*X at tot
  have shape := bBudget L
  have e : n*(SquareCaller.duration S s+8*(s*s)+16) = n*SquareCaller.duration S s+8*X+16*n := by dsimp [X]; ring
  have bC : B ≤ C := by dsimp [C]; omega
  have oC : A+J+padSteps b S.scale*b+24 ≤ C := by dsimp [C]; omega
  have rc := Nat.mul_le_mul_right X oC
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul] at rc
  have lc := Nat.mul_le_mul_right (L+1) bC
  unfold cost
  rw [e,Nat.mul_add C]
  dsimp only [J] at jf
  change _ ≤ C*(L+1)+C*X+n*SquareCaller.duration S s
  dsimp only [J] at rc
  omega

end VWZClique.IntegerRAM.Projected.Large
end

/- NativeProjectionTotalCost -/
section
namespace VWZClique.IntegerRAM.Projected
open BlockMM UniformFolds NativeTraversal WeightedProof Double

/-- A uniform charge for the whole native projected-trace instruction,
including preparation, all three dense tables, the left transform, the large
products and signed exact normalization. -/
theorem total_cost {b r : ℕ} (S : Scheme b r) (hb : 2 ≤ b) :
    ∃ A : ℕ, ∀ d ≤ 36, ∀ (H : SimpleGraph V) (π : Equiv.Perm V) (L : ℕ),
    let K := windowAt (Nat.card H.edgeSet)
    let q := tileAt (Nat.card H.edgeSet)
    let a := (qOf H L).labels.card
    let e := effectiveTile q L a
    let s := IntegerTiling.side L e
    let k := IntegerTiling.blocks L e
    Preparation.ticks d K b S.scale.toNat L +
      (Dense.cost S π (slots π H) L a + (Large.cost q S L s k +3+(13*(21*L+3)+44))) ≤
      A*(L+1)^1*(NativeTraversal.projected (SquareCaller.duration S) 1 1 L H+1) := by
  classical
  choose D largeTime using fun (H : SimpleGraph V) =>
    Large.cost_bound hb (tileAt (Nat.card H.edgeSet)) S
  let localCost (x : Fin 37 × SimpleGraph V) :=
    D x.2+Preparation.coefficient x.1 (windowAt (Nat.card x.2.edgeSet)) b S.scale.toNat
  obtain ⟨B,hB⟩ := Finite.exists_le localCost
  let C := 3*B+Dense.costCoefficient+360
  refine ⟨2*C,?_⟩
  intro d hd H π L K q a e s k
  let n := (2:ℕ)^L
  let mm := SquareCaller.duration S
  let Q := Accounting.components mm q L a
  let Y := (L+1)*Q
  have qform : Q=n^5+3*(a*n^2*mm n)+a*n^4+k*mm s+k*(s*s)+(a*n)*(a*n)+1 := rfl
  have qone : 1 ≤ Q := by omega
  have qy : Q ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have ly : L+1 ≤ Y := Nat.le_mul_of_pos_right _ qone
  have ly0 : 1 ≤ Y := by omega
  have maxH := hB (⟨d,by omega⟩,H)
  change D H+Preparation.coefficient d K b S.scale.toNat ≤ B at maxH
  have prep : Preparation.ticks d K b S.scale.toNat L ≤ B*Y :=
    (Preparation.ticks_bound ..).trans (Nat.mul_le_mul (by omega) (show n^5 ≤ Y by omega))
  have ha : a ≤ n^2 := by
    have h : a ≤ (4:ℕ)^L := by simpa [a,BasisLabel] using Finset.card_le_univ (qOf H L).labels
    exact h.trans_eq (by dsimp [n];rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul,Nat.mul_comm 2 L])
  have dense : Dense.cost S π (slots π H) L a ≤ Dense.costCoefficient*Y :=
    (Dense.cost_bound S π (slots π H) q L a ha).trans_eq (by dsimp only [Y,Q,mm];ring)
  have sq : 1 ≤ s := Nat.one_le_pow _ _ (by decide)
  have pack : 1 ≤ k := Nat.one_le_pow _ _ (by decide)
  have tile := largeTime H L s k sq pack
  change Large.cost q S L s k ≤ D H*((L+1)+k*(s*s))+k*mm s at tile
  have comb : (L+1)+k*(s*s) ≤ 2*Y := by omega
  have lbound : Large.cost q S L s k ≤ (2*B+1)*Y := by
    apply tile.trans
    calc
      _ ≤ B*(2*Y)+Y := Nat.add_le_add (Nat.mul_le_mul (by omega) comb) (by omega)
      _ = _ := by ring
  have tail : 3+(13*(21*L+3)+44) ≤ 359*Y := by omega
  have all :
      Preparation.ticks d K b S.scale.toNat L +
        (Dense.cost S π (slots π H) L a+(Large.cost q S L s k+3+(13*(21*L+3)+44))) ≤ C*Y := by
    dsimp only [C]
    rw [Nat.add_mul,Nat.add_mul, Nat.mul_assoc]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at lbound
    omega
  have paid := Accounting.unified S 1 L C H
  have endBound : C*Q ≤ (2*C)*(NativeTraversal.projected mm 1 1 L H+1) := paid
  calc
    _ ≤ C*Y := all
    _ = (L+1)*(C*Q) := by dsimp only [Y];ring
    _ ≤ (L+1)*((2*C)*(NativeTraversal.projected mm 1 1 L H+1)) := Nat.mul_le_mul_left _ endBound
    _ = _ := by simp only [pow_one];ring

end VWZClique.IntegerRAM.Projected
end

/- NativeCliqueTheorem -/
section
namespace VWZClique.IntegerRAM.Projected
open NativeTraversal NativeArena UniformFolds BlockMM

/-- The same finite bytecode is used at every input length. Both its native
square-multiplication scheme and its memory growth bound are fixed here. -/
theorem exists_kernel {b r U p : ℕ} (S : Scheme b r) (hb : 2 ≤ b) (hr : 0 < r) (hc : 0 < S.scale)
    (space : ∀ n : ℕ, 1 ≤ n → WordLayout.space b r (depth b n) 1 ≤ U*n^p) :
    Nonempty (ProjectionKernel (SquareCaller.duration S) 1) := by
  obtain ⟨A,charge⟩ := total_cost S hb
  refine ⟨{
    command := Pipeline.code S
    workspaceCoefficient := Capacity.graphCoefficient b S.scale.toNat U
    workspacePower := Capacity.power S.scale.toNat p
    timeCoefficient := A
    logPower := 1
    run := ?_ }⟩
  intro W L root output d large hL H π w stack deep bin room
  dsimp only
  intro m src
  have hd : d ≤ 36 := by omega
  obtain ⟨f,hf,o,run,done⟩ := Pipeline.execute (out:=output) S hb hr hc space large hL H π w stack hd bin room m src
  exact ⟨f,hf.trans (charge d hd H π L),o,run,done⟩

end VWZClique.IntegerRAM.Projected

theorem solution :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ k ≥ K₀,
      VWZClique.countsWithin k ((OAI.MatrixMultiplication.Arithmetic.omega ℂ - δ) * (k : ℝ) / 3) := by
  let η := (VWZClique.UniformFolds.levelSaving 36).val/8
  have hη : 0 < η := by dsimp [η]; linarith [(VWZClique.UniformFolds.levelSaving 36).pos]
  obtain ⟨b,r,hb,S,C,U,p,hc,hr,hC,rates⟩ := VWZClique.IntegerRAM.Projected.SquareCaller.choose η hη
  obtain ⟨kernel⟩ := VWZClique.IntegerRAM.Projected.exists_kernel S hb hr hc (fun n hn => (rates n hn).2)
  exact VWZClique.IntegerRAM.NativeArena.wordRam_of_projected_kernel kernel hC (fun n hn => (rates n hn).1)
end
